use crate::state_machine_chip::state_machine::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum StateBits {
    IsInvalid = 0,
    NewDict = 1,
    EndDict = 2,
    Separator = 3,
    IsKey = 4,
    IsValue = 5,
    KeyValueDelimiter = 6,
    IsStr = 7,
    IsStrEscaped = 8,
    WordBuffering = 9,
    WordComplete = 10,
}
impl StateBits {
    fn from(id: u64) -> StateBits {
        use StateBits::*;
        match id {
            0 => IsInvalid,
            1 => NewDict,
            2 => EndDict,
            3 => Separator,
            4 => IsKey,
            5 => IsValue,
            6 => KeyValueDelimiter,
            7 => IsStr,
            8 => IsStrEscaped,
            9 => WordBuffering,
            10 => WordComplete,
            _ => panic!("Invalid state bit id: {}", id),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct State(Vec<StateBits>);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SpecialChar {
    Backslash = 0x5c,
    DoubleQuote = 0x22,
    OpenBrace = 0x7b,
    CloseBrace = 0x7d,
    Colon = 0x3a,
    Comma = 0x2c,
    WhiteSpace,
    Numeric,
    Other
}

impl SpecialChar {

    fn from(ch: char) -> SpecialChar {

        use SpecialChar::*;
        match ch {
            '\\' => Backslash,
            '"' => DoubleQuote,
            '{' => OpenBrace,
            '}' => CloseBrace,
            ':' => Colon,
            ',' => Comma,
            c if c.is_whitespace() => WhiteSpace,
            c if c.is_digit(10) || c == '.' => Numeric,
            _ => Other,
        }
    }
}

pub trait StateEncoding<T> {
    fn encode(&self) -> T;
    fn decode(id: T) -> State;
}

pub trait StateCheck<B> {
    fn new() -> Self;
    fn start() -> Self;
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

pub trait JsonStateMutation<S,B,A>
where
    S: StateCheck<B>
{
    fn mutate(&self, action: A) -> Self;
}

impl<EncodeField> StateEncoding<EncodeField> for State
where
    EncodeField: From<u64> + Into<u64>,
{

    fn encode(&self) -> EncodeField
    {
        let mut state_id = 0;
        for state_bit in self.clone().0 {
            state_id += 1 << (state_bit as u64);
        }
        EncodeField::from(state_id)
    }

    fn decode(id: EncodeField) -> State
    {
        let mut state = State::new();
        let mut id = id.into();
        let mut i = 0;
        while id != 0 {
            if id % 2 == 1 {
                state.on(StateBits::from(i));
            }
            id = id >> 1;
            i += 1;
        }
        state
    }

}

use StateBits::*;

impl StateCheck<StateBits> for State {

    fn new() -> Self {
        Self( Vec::new() )
    }

    fn start() -> Self {
        Self( Vec::new() )
    }

    fn invalid() -> Self {
        Self(vec![IsInvalid])
    }

    fn on(&mut self, bit: StateBits) {
        if !self.0.contains(&bit) {
            self.0.push(bit);
        }
    }

    fn off(&mut self, bit: StateBits) {
        if self.0.contains(&bit) {
            self.0.retain(|&x| x != bit);
        }
    }

    fn flip(&mut self, bit: StateBits) {
        if self.0.contains(&bit) {
            self.0.retain(|&x| x != bit);
        } else {
            self.0.push(bit);
        }
    }

    fn check(&self, bit: StateBits) -> bool {
        self.0.contains(&bit)
    }

    fn is_null(&self) -> bool {
        self.0.is_empty()
    }

    fn check_and(&self, bits: Vec<StateBits>) -> bool {
        bits.iter().all(|&bit| self.0.contains(&bit))
    }

    fn check_or(&self, bits: Vec<StateBits>) -> bool {
        bits.iter().any(|&bit| self.0.contains(&bit))
    }

    fn assert_valid(&self) {
        assert!(!self.check(IsInvalid), "Invalid state found");
    }

}

impl<S> JsonStateMutation<S, StateBits, SpecialChar> for S
where
    S: StateCheck<StateBits> + Clone
{

    fn mutate(&self, action: SpecialChar) -> Self {

        use SpecialChar::*;
        let mut state = self.clone();

        // Propagate the invalid state
        if state.check(IsInvalid) {
            return state;
        }

        // Complete unconditional step mutations
        if state.check(NewDict){
            state.on(IsKey);
            state.off(NewDict);
        }
        if state.check(EndDict){
            state.on(WordComplete); // for outer state
            state.off(EndDict);
        }
        if state.check(Separator){
            state.on(IsKey);
            state.off(Separator);
        }
        if state.check(KeyValueDelimiter){
            state.on(IsValue);
            state.off(KeyValueDelimiter);
        }

        // Match logic
        if state.check(IsStrEscaped) {
            state.off(IsStrEscaped);

        } else if state.is_null(){
            
            match action {
                    
                OpenBrace => {
                    state.on(NewDict);
                },

                WhiteSpace => {
                    // Do nothing
                },

                _ => {
                    state = S::invalid();
                }

            }

        } else if state.check(IsStr){

            match action {

                Backslash => {
                    state.on(IsStrEscaped);
                },

                DoubleQuote => {
                    state.on(WordComplete);
                    state.off(WordBuffering);
                    state.off(IsStr);
                },

                _ => {
                    state.on(IsStr);
                }

            }

        } else {

            match action {

                OpenBrace => {
                    if state.check(IsValue) && !state.check(WordComplete) {
                        state.on(NewDict);
                        state.off(IsValue);
                    } else {
                        state = S::invalid();
                    }
                }, 

                CloseBrace => {
                    if state.check(IsValue) {
                        state.on(EndDict);
                        state.off(WordComplete); // For inner states
                        state.off(WordBuffering); // just in case value is ... 123}
                    } else {
                        state = S::invalid();
                    }
                },

                Comma => {
                    if state.check(IsValue) {
                        state.on(Separator);
                        state.off(IsValue);
                        state.off(WordComplete);
                        state.off(WordBuffering); // just in case value is ... 123,
                    } else {
                        state = S::invalid();
                    }
                },

                Colon => {
                    if state.check(IsKey) {
                        state.on(KeyValueDelimiter);
                        state.off(IsKey);
                        state.off(WordComplete);
                    } else {
                        state = S::invalid();
                    }
                },

                DoubleQuote => {
                    if state.check(WordComplete) {
                        state = S::invalid();
                    } else {
                        state.on(IsStr);
                        state.on(WordBuffering);
                    }
                },

                WhiteSpace => {
                    if state.check_and(vec![IsValue, WordBuffering]) {
                        state.on(WordComplete);
                        state.off(WordBuffering);
                    }
                },

                // TODO: A small bug with more than one decimal point, which should be invalid but is not
                Numeric => {
                    if state.check(IsValue) && !state.check(WordComplete) {
                        state.on(WordBuffering);
                    } else {
                        state = S::invalid();
                    } 
                },

                _ => state = S::invalid(),
            }
        }

        state
    }
}

// Generate a lookup table
mod gen_lookup {

        use super::*;
        use std::collections::HashSet;
    
        pub fn bfs_gen_lookup_table() -> Vec<(u64, u64, char)> {
    
            let mut lookup_table: Vec<(u64, u64, char)> = vec![];
            let mut bfs_buffer: Vec<u64> = vec![];
            let mut bfs_memory: HashSet<u64> = HashSet::new();

            // BFS
            bfs_buffer.push(State::encode(&State::start()));
            while !bfs_buffer.is_empty() {

                let before = bfs_buffer.pop().unwrap();
                let state = State::decode(before);
                bfs_memory.insert(before);

                for j in 0..=255 {

                    let c = char::from(j);
                    let action = SpecialChar::from(c);
                    
                    let end_state = state.mutate(action);
                    let after: u64 = end_state.encode();

                    let row = (before, after, c);
                    lookup_table.push(row);
                    if !bfs_memory.contains(&after) && !bfs_buffer.contains(&after){
                        bfs_buffer.push(after);
                    }
                }
            }

            lookup_table

        }
    
        #[cfg(test)]
        mod tests {
    
            use super::*;
            use std::fs::File;
            use std::io::Write;
    
            #[test]
            fn test_gen_lookup_table() {

                let lookup_table = bfs_gen_lookup_table();
                let mut file = File::create("./data/lookup_table.txt").expect("Unable to create file");

                for row in lookup_table {

                    let begin = State::decode(row.0);
                    let action = SpecialChar::from(row.2 as char);
                    let end: u64 = begin.mutate(action).encode();

                    let line = format!("{:?} {:?} {:?}", row.0, row.1, row.2);
                    assert_eq!(end, row.1);
                    writeln!(file, "{}", line).expect("Unable to write data");
                }

            }
    
        }

}


// Test cases
#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_state_check() {
        let mut state = State::start();
        assert_eq!(state.check(IsValue), true);
        assert_eq!(state.check(IsKey), false);
        state.on(IsKey);
        assert_eq!(state.check(IsKey), true);
        state.off(IsKey);
        assert_eq!(state.check(IsKey), false);
        state.flip(IsKey);
        assert_eq!(state.check(IsKey), true);
        state.flip(IsKey);
        assert_eq!(state.check(IsKey), false);
    }

    #[test]
    fn test_state_check_and() {
        let mut state = State::start();
        assert_eq!(state.check_and(vec![IsValue, IsKey]), false);
        state.on(IsKey);
        assert_eq!(state.check_and(vec![IsValue, IsKey]), true);
    }

    #[test]
    fn test_state_check_or() {
        let mut state = State::start();
        assert_eq!(state.check_or(vec![IsValue, IsKey]), true);
        state.off(IsValue);
        assert_eq!(state.check_or(vec![IsValue, IsKey]), false);
        state.on(IsKey);
        assert_eq!(state.check_or(vec![IsValue, IsKey]), true);
    }

    #[test]
    fn test_state_mutation() {
        
        let input = "{\"a{}  \": 123  , \"b\\\"a\": \"xyz\"}".to_string();
        let mut state = State::start();
        let mut transcript = vec![state.clone()];

        for c in input.chars() {
            let action = SpecialChar::from(c);
            let end_state = state.mutate(action);
            println!("Reading {:?} with starting state {:?} to ending state {:?}", c, state, end_state);
            end_state.assert_valid();
            transcript.push(end_state.clone());
            state = end_state;
        }
    }

    #[test]
    fn test_encoding_decoding() {
        
        let input = "   {\"a{}  \": 123  , \"b\\\"a\": \"xyz\"}".to_string();
        let mut state = State::start();
        let mut transcript = vec![state.clone()];

        for c in input.chars() {
            let action = SpecialChar::from(c);
            let end_state = state.mutate(action);
            let encoding: u64 = end_state.encode();
            let decode_encode: u64 = State::decode(encoding).encode();
            println!("Reading {:?} with ending state \t {:?} \t encoding {:?}", c, encoding, State::decode(encoding));
            end_state.assert_valid();
            assert_eq!(encoding, decode_encode);
            transcript.push(end_state.clone());
            state = end_state;
        }
    }

}

