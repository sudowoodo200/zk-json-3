use clap::error;
use halo2_base::{
    gates::flex_gate::{GateChip, FlexGateConfig, GateInstructions, GateStrategy, MAX_PHASE},
    halo2_proofs::{
        circuit::{Layouter, Value},
        plonk::{
            Advice, Column, ConstraintSystem, Error, SecondPhase, Selector, TableColumn, ThirdPhase,
            Assigned
        },
        poly::Rotation,
    },
    utils::{
        ScalarField,
    },
    AssignedValue, Context,
    QuantumCell::{self, Constant, Existing, Witness},
};
use crate::state_machine_chip::json_state_machine::{State, SpecialChar, StateEncoding, StateCheck, JsonStateMutation, StateBit};

use super::state_machine::StateMachine;


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
    pub transcript: Column<Advice>,
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

        let transcript = meta.advice_column();
        let q_lookup = meta.complex_selector();
        let lookup = [();3].map(|_| meta.lookup_table_column());

        meta.enable_equality(transcript);

        let config = Self {
            gate,
            transcript,
            q_lookup,
            lookup,
            _strategy: state_machine_strategy,
        };

        config.create_lookup(meta);

        // Assert conditions

        config
        
    }
    

    fn create_lookup(&self, meta: &mut ConstraintSystem<F>) {

        meta.lookup(
            "State Transition Lookups", 
            |meta| {
                let ql = meta.query_selector(self.q_lookup); // only turned on for odd idx
                let curr_state = meta.query_advice(self.transcript, Rotation::cur());
                let mutation = meta.query_advice(self.transcript, Rotation::next());
                let next_state = meta.query_advice(self.transcript, Rotation(2));

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
    pub transition_table: Vec<(F, F, F)>,
}

pub trait StateMachineInstructions<F: ScalarField> {

    type Gate: GateInstructions<F>;

    fn gate(&self) -> &Self::Gate;
    fn strategy(&self) -> StateMachineStrategy;
    fn next_state(&self, start: F, action: F) -> F;
    fn mutate_state(
        &self,
        ctx: &mut Context<F>,
        start: impl Into<QuantumCell<F>>,
        action: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>;

}

impl<F> StateMachineChip<F>
where F: ScalarField + JsonStateMutation<State, StateBit, SpecialChar> + StateEncoding<u64>
{
    pub fn new(strategy: StateMachineStrategy, transition_table:Vec<(F,F,F)>) -> Self{
        let gate = GateChip::new(
            match strategy {
                StateMachineStrategy::Vertical => GateStrategy::Vertical,
            },
        );

        Self {
            strategy,
            gate,
            transition_table,
        }
    }
}

impl<F> StateMachineInstructions<F> for StateMachineChip<F>
where
    F: ScalarField
{

    type Gate = GateChip<F>;

    fn gate(&self) -> &Self::Gate {
        &self.gate
    }

    fn strategy(&self) -> StateMachineStrategy {
        self.strategy
    }

    fn next_state(&self, start: F, action: F) -> F {
        let mut next_state = start;
        let mut mutation = action;
        for (start_state, end_state, action_flag) in self.transition_table.iter() {
            if start == *start_state && action == *action_flag {
                next_state = *end_state;
            }
        }
        next_state
    }

    fn mutate_state(
        &self,
        ctx: &mut Context<F>,
        start: impl Into<QuantumCell<F>>,
        action: impl Into<QuantumCell<F>>,
    ) -> AssignedValue<F>  {

        fn unpack<F: ScalarField>(qc: impl Into<QuantumCell<F>>) -> F {

            fn unpack_assignedvalue<F: ScalarField>(av: AssignedValue<F>) -> F {
                match av.value {
                    Assigned::Trivial(av) => av,
                    _ => panic!("Invalid assigned value"),
                }
            }

            let value = match qc.into() {
                QuantumCell::Existing(f) => unpack_assignedvalue(f),
                QuantumCell::Witness(f) => f,
                QuantumCell::Constant(f) => f,
                _ => panic!("Invalid start state"),
            };

            value 
        }
        let start_f = unpack(start);
        let action_f = unpack(action);
        let next_f = self.next_state(start_f, action_f);

        // THIS IS almost 100% WRONG....
        // Intent is to assign the incremental action, state pair to the column
        // How do you initialize the first row? How do you choose which selector to flip?
        // | s_0 | a_0 | s_1 | a_1 | ... 
        ctx.assign_region(
            [Witness(action_f), Witness(next_f)],
            [1]
        );
        ctx.get(-1)
        
    }

}

// TODO: I think I need to make a builder...