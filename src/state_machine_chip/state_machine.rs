/// Abstract State Machine =============================================
/// Not yet in use. This is meant to work well with Halo2 Fields
/// Using a hard coded look up table for now instead.


use std::ops::{Add, Sub, Mul, Div, Rem};
use num_traits::{Pow, NumCast, Zero, One};
use std::marker::PhantomData;
use std::hash::{Hash};

pub trait StateBit: From<u8> + Into<u8> + Copy + Eq {
    fn error_bit() -> Self;
}
pub trait StateAction: From<u64> + Into<u64> + Copy + Eq + PartialEq + Ord {}
pub trait EncodingField: Add<Output=Self> + Sub<Output=Self> + Mul<Output=Self> 
                        + Div<Output=Self> + Pow<u32, Output=Self> + Eq + PartialEq
                        + Rem<u64, Output=Self> + Copy + NumCast + One + Zero + Hash
{
    // shift left and right arithmetics
    fn shr(&self, rhs: u8) -> Self {
        *self / (Self::from(2).unwrap().pow(rhs as u32))
    }

    fn shl(&self, rhs: u8) -> Self {
        *self * (Self::from(2).unwrap().pow(rhs as u32))
    }
}
impl EncodingField for u64 {}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State<B>(Vec<B>);

pub trait StateEncoding<F> 
{
    type EncodingField;
    fn encode(&self) -> F;
    fn decode(id: F) -> Self;
}

pub trait StateCheck<B> {
    fn new() -> Self;
    fn invalid() -> Self;
    fn on(&mut self, bit: B);
    fn off(&mut self, bit: B);
    fn flip(&mut self, bit: B);
    fn check(&self, bit: B) -> bool;
    fn is_null(&self) -> bool;
    fn check_or(&self, bits: Vec<B>) -> bool;
    fn check_and(&self, bits: Vec<B>) -> bool;
    fn assert_valid(&self);
}

impl<B, F> StateEncoding<F> for State<B>
where 
    B: StateBit,
    F: EncodingField 
{

    type EncodingField = F;

    fn encode(&self) -> F
    {
        let mut state_id = F::zero();
        for state_bit in self.clone().0 {
            state_id = state_id + F::one().shl(state_bit.into());
        }
        state_id
    }

    fn decode(id: F) -> State<B>
    {
        let mut state = State::new();
        let mut idx = id;
        let mut i = 0;
        while idx != F::zero() {
            if idx % 2 == F::one() {
                state.on(B::from(i));
            }
            idx = idx.shr(1);
            i += 1;
        }
        state
    }

}

impl<B> StateCheck<B> for State<B> 
where
    B: StateBit
{

    fn new() -> Self {
        Self( Vec::new() )
    }

    fn invalid() -> Self {
        Self(vec![B::error_bit()])
    }

    fn on(&mut self, bit: B) {
        if !self.0.contains(&bit) {
            self.0.push(bit);
        }
    }

    fn off(&mut self, bit: B) {
        if self.0.contains(&bit) {
            self.0.retain(|&x| x != bit);
        }
    }

    fn flip(&mut self, bit: B) {
        if self.0.contains(&bit) {
            self.0.retain(|&x| x != bit);
        } else {
            self.0.push(bit);
        }
    }

    fn check(&self, bit: B) -> bool {
        self.0.contains(&bit)
    }

    fn is_null(&self) -> bool {
        self.0.is_empty()
    }

    fn check_and(&self, bits: Vec<B>) -> bool {
        bits.iter().all(|&bit| self.0.contains(&bit))
    }

    fn check_or(&self, bits: Vec<B>) -> bool {
        bits.iter().any(|&bit| self.0.contains(&bit))
    }

    fn assert_valid(&self) {
        assert!(!self.check(B::error_bit()), "Invalid state found");
    }

}

pub struct StateMachine<A, B> 
{
    pub state: State<B>,
    pub mutation: Box<dyn FnMut(&State<B>, A) -> State<B>>,
    _phantom: PhantomData<B>,
}

impl<A, B> StateMachine<A, B> 
where
    A: StateAction,
    B: StateBit,
{

    pub fn begin() -> Self {
        let s = State::new();
        Self {  state : s, 
                mutation : Box::new(| state: &State<B>, action | state.clone()),
                _phantom: PhantomData
            }
    }

    pub fn step(&mut self, a: A) {
        self.state = (self.mutation)(&self.state, a);
    }

    pub fn preview_step(&mut self, a: A) -> State<B> {
        (self.mutation)(&self.state, a)
    }

    pub fn set_mutation_fn(&mut self, mutation: Box<dyn FnMut(&State<B>, A) -> State<B>>) {
        self.mutation = mutation;
    }

    pub fn get_state(&self) -> State<B> {
        self.state.clone()
    }

    pub fn encode<F: EncodingField>(&self) -> F {
        self.state.encode()
    }

    pub fn decode_and_update<F: EncodingField>(&mut self, id: F){
        self.state = State::decode(id);
    }

}

// Generate a lookup table
mod gen_lookup {

    use super::*;
    use std::collections::HashSet;

    pub fn bfs_gen_lookup_table<A,B,F>(action_set: Vec<A>) -> Vec<(F, F, A)>
    where
        A: StateAction,
        B: StateBit,
        F: EncodingField,
    {

        let mut lookup_table: Vec<(F, F, A)> = vec![];
        let mut bfs_buffer: Vec<F> = vec![];
        let mut bfs_memory: HashSet<F> = HashSet::new();
        let mut state_machine = StateMachine::<A, B>::begin();

        // BFS
        bfs_buffer.push(state_machine.encode::<F>());
        while !bfs_buffer.is_empty() {

            let before = bfs_buffer.pop().unwrap();
            bfs_memory.insert(before);

            state_machine.decode_and_update::<F>(before);
            for a in action_set.iter() {
                let action = a.clone();
                let after = state_machine.preview_step(action).encode();
                let row = (before, after, action);
                lookup_table.push(row);
                if !bfs_memory.contains(&after) && !bfs_buffer.contains(&after){
                    bfs_buffer.push(after);
                }
            }
        }

        lookup_table

    }

}


