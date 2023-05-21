use halo2_base::{
    gates::flex_gate::{GateChip, FlexGateConfig, GateInstructions, GateStrategy, MAX_PHASE},
    halo2_proofs::{
        circuit::{Layouter, Value},
        plonk::{
            Advice, Column, ConstraintSystem, Error, SecondPhase, Selector, TableColumn, ThirdPhase,
        },
        poly::Rotation,
    },
    utils::{
        biguint_to_fe, bit_length, decompose_fe_to_u64_limbs, fe_to_biguint, BigPrimeField,
        ScalarField,
    },
    AssignedValue, Context,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::state_machine_chip::json_state_machine::{State, SpecialChar, StateEncoding, StateCheck, JsonStateMutation, StateBit};


/// Specifies the gate strategy -- aligning with rest of system
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum StateMachineStrategy {
    /// # Vertical Gate Strategy:
    /// `q_0 * (a + b * c - d) = 0`
    /// where
    /// * a = value[0], b = value[1], c = value[2], d = value[3]
    /// * q = q_lookup[0]
    /// * q is either 0 or 1 so this is just a simple selector
    ///
    /// Using `a + b * c` instead of `a * b + c` allows for "chaining" of gates, i.e., the output of one gate becomes `a` in the next gate.
    Vertical, // vanilla implementation with vertical basic gate(s)
}


/// Configuration for State Machine
/// begin_states | end_states | transition
#[derive(Clone, Debug)]
pub struct StateMachineConfig<F: ScalarField> {

    pub gate: FlexGateConfig<F>,
    pub states: Column<Advice>,
    pub mutation: Column<Advice>,
    pub q_lookup: Selector,
    pub lookup: [TableColumn; 3],
    _strategy: StateMachineStrategy,

}

/// State Machine Gate
impl<F: ScalarField> StateMachineConfig<F> {

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        state_machine_strategy: StateMachineStrategy,
        num_advice: &[usize],
        num_fixed: usize,
        circuit_degree: usize,
    ) -> Self {

        let gate = FlexGateConfig::configure(
            meta,
            match state_machine_strategy {
                StateMachineStrategy::Vertical => GateStrategy::Vertical,
            },
            num_advice,
            num_fixed,
            circuit_degree,
        );

        let states = meta.advice_column();
        let mutation = meta.advice_column();
        let q_lookup = meta.complex_selector();
        let lookup = [();3].map(|_| meta.lookup_table_column());

        meta.enable_equality(states);
        meta.enable_equality(mutation);

        let config = Self {
            gate,
            states,
            mutation,
            q_lookup,
            lookup,
            _strategy: state_machine_strategy,
        };

        config.create_lookup(meta);

        // Assert conditions

        config
        
    }
    

    fn create_lookup(&self, meta: &mut ConstraintSystem<F>) {

        meta.create_gate(
            "State must start from 0",
            |meta| {
                let ql = meta.query_selector(self.q_lookup);
                let curr_state = meta.query_advice(self.states, Rotation::cur());
                vec![
                    ql * curr_state
                ]
            },
        );

        meta.lookup(
            "State Transition Lookups", 
            |meta| {
                let ql = meta.query_selector(self.q_lookup);
                let curr_state = meta.query_advice(self.states, Rotation::cur());
                let next_state = meta.query_advice(self.states, Rotation::next());
                let mutation = meta.query_advice(self.mutation, Rotation::cur());

                vec![
                    (ql.clone() * curr_state, self.lookup[0]),
                    (ql.clone() * next_state, self.lookup[1]),
                    (ql * mutation, self.lookup[2]),
                ]
            }
        );

    }

    fn load_lookup_table(&self, layouter: &mut impl Layouter<F>) -> Result<(),Error>{

        // load data from text file
        // use std::fs::File;
        // use std::io::{BufRead, BufReader};

        let mut contents: Vec<(u64, u64, char)> = Vec::new();
        // let file = File::open("./data/state_transition_table.txt").expect("Failed to open file");
        // let reader = BufReader::new(file);
        // for line in reader.lines(){
        //     let row = line.unwrap();
        //     let buffer: Vec<_> = row.split_ascii_whitespace().collect();
        //     let start_state = buffer[0].parse::<u64>().unwrap();
        //     let end_state = buffer[1].parse::<u64>().unwrap();
        //     let mutation = buffer[2].parse::<char>().unwrap();
        //     contents.push((start_state, end_state, mutation));
        // }

        // Test lookup
        contents.push((0, 1, 'a'));
        contents.push((1, 2, 'b'));


        // metadata
        let n = contents.len();
        let columns = vec![(0, "begin_state"), (1, "end_state"), (2, "mutation")];

        // build lookup table
        layouter.assign_table(
            || "State Transition Table", 
            |mut table| {

                for col in columns.clone() {
                    for idx in 0..n {

                        let value = match col.0 {
                            0 => contents[idx].0,
                            1 => contents[idx].1,
                            2 => contents[idx].2 as u64,
                            _ => unreachable!(),
                        };

                        table.assign_cell(
                              || format!("State Transition Table: row {:?} {:?}", idx, col.1),
                              self.lookup[col.0],
                              idx,
                              || Value::known(F::from(value)),
                        )?;  
                    }
                }
                Ok(())
            }
        )?;

        Ok(())
    }
    
}

#[derive(Clone, Debug)]
pub struct StateMachineChip<F: ScalarField> {
    strategy: StateMachineStrategy,
    pub gate: GateChip<F>,
    pub state_machine: State,
}

pub trait StateMachineInstructions<F: ScalarField> {

    type Gate: GateInstructions<F>;

    fn gate(&self) -> &Self::Gate;
    fn strategy(&self) -> StateMachineStrategy;
    fn mutate_state(
        &self,
        start: impl Into<QuantumCell<F>>,
        action: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>;

}

impl<F> StateMachineInstructions<F> for StateMachineChip<F>
where
    F: ScalarField + JsonStateMutation<State, StateBit, SpecialChar> + StateEncoding<u64>
{

    type Gate = GateChip<F>;

    fn gate(&self) -> &Self::Gate {
        &self.gate
    }

    fn strategy(&self) -> StateMachineStrategy {
        self.strategy
    }

    fn mutate_state(
        &self,
        start: impl Into<QuantumCell<F>>,
        action: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>  {

        let id = start.into().value().clone();
        let start = State::decode(start.into().value().clone());
        // let action = SpecialChar::from(action.into().value() as char);

        let end = start.mutate(action);

        // TODO: Field Abstraction Issues for encoder
        // I believe ScalarField does not support From<u64> and Into<u64> operations, which breaks trait bounds for StateEncoding
        // StateEncoding must be implemented to support generic fields; only need >> and << operations
        // Go through the QuantumCell abstraction again to make sure it is correct

        // TODO: Enum Abstraction Issues for Action
        // We should reimplement From for SpecialChar to support generic fields, instead of relying on chars

        
    }

}

// TODO: Need a Builder