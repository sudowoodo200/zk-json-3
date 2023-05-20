#![allow(unused_imports)]
use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    halo2curves::FieldExt,
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector},
    poly::Rotation,
};
use std::cell::RefCell;
use std::fmt::Display;

// Chip for reading JSON strings
// Consider the following json string: {"x": {"a{\""}":1}}. We want to prove that x["a{}"] == 1
// (1) Validity check. Raw string is in the first column; not_esc tracks "{" chars in quotes " " / ' '
//      | raw   | [special_chars]   | not_str   | str_escaped   | level     | [query]    | struct_selector       | [start/end_select]  |
//      | {     | ...               | 1         | 0             | 1         | ...        | 0                     | 1                   |
//      | "     | ...               | 0         | 0             | 1         | ...        | 1                     | 0                   |
//      | x     | ...               | 0         | 0             | 1         | ...        | 1                     | 0                   |
//      | "     | ...               | 1         | 0             | 1         | ...        | 1                     | 0                   |
//      | :     | ...               | 1         | 0             | 1         | ...        | 1                     | 0                   |
//      | {     | ...               | 1         | 0             | 2         | ...        | 1                     | 0                   |
//      | "     | ...               | 0         | 0             | 2         | ...        | 1                     | 0                   |
//      | a     | ...               | 0         | 0             | 2         | ...        | 1                     | 0                   |
//      | \     | ...               | 0         | 1             | 2         | ...        | 1                     | 0                   |
//      | "     | ...               | 0         | 0             | 2         | ...        | 1                     | 0                   |
//      | {     | ...               | 0         | 0             | 2         | ...        | 1                     | 0                   |
//      | }     | ...               | 0         | 0             | 2         | ...        | 1                     | 0                   |
//      | "     | ...               | 1         | 0             | 2         | ...        | 1                     | 0                   |
//      | :     | ...               | 1         | 0             | 2         | ...        | 1                     | 0                   |
//      | 1     | ...               | 1         | 0             | 2         | ...        | 1                     | 0                   |
//      | }     | ...               | 1         | 0             | 1         | ...        | 1                     | 0                   |
//      | }     | ...               | 1         | 0             | 0         | ...        | 0                     | 1                   |

// (2) Query check matches both the level and the key, value pairs
//      TBD
//      - Can use halo2-lib more extensively here for substring matching
//      - For efficiency, share the raw column
// (3) TODO
//      - DEFER to Regex: form of keys and values
//      - DEFER to RLC: Substring existence
//      - Support variable hidden rows to mask the length of the string


#[derive(Clone, Copy, Debug)]
pub struct JsonConfig {

    raw: Column<Advice>,

    backslash_inv: Column<Advice>,
    double_quote_inv: Column<Advice>,
    open_brace_inv: Column<Advice>,
    close_brace_inv: Column<Advice>,

    backslash: Column<Advice>,      // \
    double_quote: Column<Advice>,   // "
    open_brace: Column<Advice>,     // {
    close_brace: Column<Advice>,    // }

    not_str: Column<Advice>,
    str_escaped: Column<Advice>,
    level: Column<Advice>,
    level_inv: Column<Advice>,

    body_selector: Selector,
    start_selector: Selector,
    end_selector: Selector,
    json_all: Selector,
}

impl JsonConfig {

    pub fn configure<F: FieldExt>(meta: &mut ConstraintSystem<F>) -> Self {

        let [ raw, backslash_inv, double_quote_inv, open_brace_inv, 
                close_brace_inv, backslash, double_quote, open_brace, 
                close_brace, not_str, str_escaped, level, level_inv] = [(); 13].map(|_| meta.advice_column());

        let body_selector = meta.selector();
        let start_selector = meta.selector();
        let end_selector = meta.selector();
        let json_all = meta.selector();

        [raw, backslash_inv, double_quote_inv, open_brace_inv, close_brace_inv, 
         backslash, double_quote, open_brace, close_brace, not_str, str_escaped, level, level_inv].map(|column| meta.enable_equality(column));

        // Set boolean columns to 0 or 1
        meta.create_gate("Booleans", |meta|{

            let e = meta.query_advice(not_str, Rotation::cur());
            let bs = meta.query_advice(backslash, Rotation::cur());
            let dq = meta.query_advice(double_quote, Rotation::cur());
            let ob = meta.query_advice(open_brace, Rotation::cur());
            let cb = meta.query_advice(close_brace, Rotation::cur());
            let str_esc = meta.query_advice(str_escaped, Rotation::cur());

            let all = meta.query_selector(json_all);

            let one = Expression::Constant(F::one());
            let expr_1 = all.clone() * e.clone() * (one.clone() - e);
            let expr_2 = all.clone() * bs.clone() * (one.clone() - bs);
            let expr_3 = all.clone() * dq.clone() * (one.clone() - dq);
            let expr_4 = all.clone() * ob.clone() * (one.clone() - ob);
            let expr_5 = all.clone() * cb.clone() * (one.clone() - cb);
            let expr_6 = all.clone() * str_esc.clone() * (one.clone() - str_esc.clone());

            vec![expr_1, expr_2, expr_3, expr_4, expr_5, expr_6]

        });

        // Set char flags
        // TODO:
        //     - Can you simplify this with lookup?
        meta.create_gate("Char booleans", |meta| {

            let r = meta.query_advice(raw, Rotation::cur());
            let bs = meta.query_advice(backslash, Rotation::cur());
            let dq = meta.query_advice(double_quote, Rotation::cur());
            let ob = meta.query_advice(open_brace, Rotation::cur());
            let cb = meta.query_advice(close_brace, Rotation::cur());

            let bs_inv = meta.query_advice(backslash_inv, Rotation::cur());
            let dq_inv = meta.query_advice(double_quote_inv, Rotation::cur());
            let ob_inv = meta.query_advice(open_brace_inv, Rotation::cur());
            let cb_inv = meta.query_advice(close_brace_inv, Rotation::cur());

            let struct_s = meta.query_selector(body_selector);

            let one = Expression::Constant(F::one());

            // if not matched, set flag = 0
            let expr_1 = struct_s.clone() * (r.clone() - Expression::Constant(F::from(0x5c))) * bs.clone();
            let expr_2 = struct_s.clone() * (r.clone() - Expression::Constant(F::from(0x22))) * dq.clone();
            let expr_3 = struct_s.clone() * (r.clone() - Expression::Constant(F::from(0x7b))) * ob.clone();
            let expr_4 = struct_s.clone() * (r.clone() - Expression::Constant(F::from(0x7d))) * cb.clone();

            // If match, flag = 1. Requires an inversion column. See is_zero.rs
            let expr_5 = struct_s.clone() * ((r.clone() - Expression::Constant(F::from(0x5c))) * bs_inv.clone() + bs.clone() - one.clone());
            let expr_6 = struct_s.clone() * ((r.clone() - Expression::Constant(F::from(0x22))) * dq_inv.clone() + dq.clone() - one.clone());
            let expr_7 = struct_s.clone() * ((r.clone() - Expression::Constant(F::from(0x7b))) * ob_inv.clone() + ob.clone() - one.clone());
            let expr_8 = struct_s.clone() * ((r.clone() - Expression::Constant(F::from(0x7d))) * cb_inv.clone() + cb.clone() - one.clone());

            vec![expr_1, expr_2, expr_3, expr_4, expr_5, expr_6, expr_7, expr_8]

        });

        // Check terminal conditions
        meta.create_gate("Terminal conditions", |meta| {

            let r = meta.query_advice(raw, Rotation::cur());
            let bs = meta.query_advice(backslash, Rotation::cur());
            let dq = meta.query_advice(double_quote, Rotation::cur());
            let ob = meta.query_advice(open_brace, Rotation::cur());
            let cb = meta.query_advice(close_brace, Rotation::cur());
            let e = meta.query_advice(not_str, Rotation::cur());
            let l = meta.query_advice(level, Rotation::cur());

            let start_s = meta.query_selector(start_selector);
            let end_s = meta.query_selector(end_selector);

            let one = Expression::Constant(F::one());

            // start conditions
            let expr_1 = start_s.clone() * (r.clone() - Expression::Constant(F::from(0x7b))); // raw = { 
            let expr_2 = start_s.clone() * (one.clone() - e.clone()); // booleans e = 1
            let expr_3 = start_s.clone() * (one.clone() - ob.clone()); // booleans ob = 1
            let expr_4 = start_s.clone() * bs.clone(); // booleans bs = 0
            let expr_5 = start_s.clone() * cb.clone();
            let expr_6 = start_s.clone() * dq.clone();
            let expr_7 = start_s.clone() * (l.clone() - one.clone()); // level = 1
            let expr_8 = start_s * (l.clone() - one.clone()); // level = 1

            // end conditions
            let expr_9 = end_s.clone() * (one.clone() - e.clone()); // booleans e = 1
            let expr_10 = end_s.clone() * (one.clone() - cb.clone()); // booleans cb = 1; note that this forces r = }

            vec![expr_1, expr_2, expr_3, expr_4, expr_5, expr_6, expr_7, expr_8, expr_9, expr_10]

        });

        // Toggle not_str depending on whether raw[row] is in a nested string
        // Supports:
        //      - " " quotes (JSON doesn't allow single quotes anyway)
        //      - \" escaping
        meta.create_gate("Toggle not_str", |meta| {

            let dq = meta.query_advice(double_quote, Rotation::cur());
            let e = meta.query_advice(not_str, Rotation::cur());
            let e_prev = meta.query_advice(not_str, Rotation(-1));
            let str_esc_prev = meta.query_advice(str_escaped, Rotation(-1));

            let struct_s = meta.query_selector(body_selector);

            let one = Expression::Constant(F::one());
            let expr_1 = struct_s.clone() * (one.clone() - dq.clone()) * (e.clone() - e_prev.clone()); // if r != " then e == e_prev
            let expr_2 = struct_s.clone() * dq.clone() * (one.clone() - str_esc_prev.clone()) * (e.clone() + e_prev.clone() - one.clone()); // if r == " and str_esc_prev != 1 then e + e_prev == 1

            vec![expr_1, expr_2]

        });

        // Handle backslash escapes
        meta.create_gate("Backslash escaping", |meta| {

            let bs = meta.query_advice(backslash, Rotation::cur());
            let ns = meta.query_advice(not_str, Rotation::cur());
            let str_esc = meta.query_advice(str_escaped, Rotation::cur());
            let str_esc_prev = meta.query_advice(str_escaped, Rotation(-1));

            let struct_s = meta.query_selector(body_selector);

            let one = Expression::Constant(F::one());
            let expr_1 = struct_s.clone() * ns.clone() * bs.clone(); // if not_str == 1 then bs == 0; no backslash chars in non-strings
            let expr_2 = struct_s.clone() *  str_esc_prev.clone() * str_esc.clone(); // if str_esc_prev, then str_esc == 0
            let expr_3 = struct_s.clone() * (one.clone() - ns.clone()) * (one.clone() - str_esc_prev.clone()) * (bs.clone() - str_esc.clone()); // if not_str == 0 and not already escaped, then str_escape == backslash

            vec![expr_1, expr_2, expr_3]

        });

        // Start at level 0 and +1 for every { in raw and -1 for every } in raw, if not_esc == 1
        meta.create_gate("Count {} levels", |meta| {

            let ob = meta.query_advice(open_brace, Rotation::cur());
            let cb = meta.query_advice(close_brace, Rotation::cur());
            let l = meta.query_advice(level, Rotation::cur());
            let l_prev = meta.query_advice(level, Rotation(-1));
            let not_str = meta.query_advice(not_str, Rotation::cur());

            let struct_s = meta.query_selector(body_selector);
            let end_s = meta.query_selector(end_selector);

            let one = Expression::Constant(F::one());
            let expr_1 = struct_s.clone() * (one.clone() - ob.clone() - cb.clone()) * (l.clone() - l_prev.clone()); // if r != { or } then l == l_prev
            let expr_2 = struct_s.clone() * not_str.clone() * ob.clone() * (l.clone() - l_prev.clone() - one.clone()); // if r == { and not_str then l == l_prev + 1
            let expr_3 = struct_s.clone() * not_str.clone() * cb.clone() * (l.clone() - l_prev.clone() + one.clone()); // if r == } and not_str then l == l_prev - 1
            let expr_4 = end_s.clone() * not_str.clone() * cb.clone() * (l.clone() - l_prev.clone() + one.clone()); // if r == } then l == l_prev - 1 at the end,

            vec![expr_1, expr_2, expr_3, expr_4]
            
        });

        // Check that the JSON level structure is valid
        meta.create_gate("Check level structure", |meta| {

            let l = meta.query_advice(level, Rotation::cur());
            let l_inv = meta.query_advice(level_inv, Rotation::cur());

            let end_s = meta.query_selector(end_selector);
            let struct_s = meta.query_selector(body_selector);

            let one = Expression::Constant(F::one());
            let expr_1 = end_s.clone() * l.clone(); // if end_s, level == 0
            let expr_2 = struct_s.clone() * (one - l * l_inv ); // if struct_s, level > 0

            vec![expr_1, expr_2]

        });

        Self { raw, backslash_inv, double_quote_inv, open_brace_inv, close_brace_inv, backslash, double_quote, 
            open_brace, close_brace, not_str, str_escaped, level, level_inv, body_selector, start_selector, end_selector, json_all }

    }

}

// The circuit struct; F should be u8 or u16
#[derive(Clone, Default)]
pub struct JsonCircuit<F: FieldExt> {
    pub raw: Vec<Value<F>>,
    // pub key: Vec<F>
    // pub value: Vec<F>
}

// Implementation. Right now it only supports checking that the JSON is structurally valid
// TODO: 
//  - Need to compose this with RLC for the query
impl<F: FieldExt> Circuit<F> for JsonCircuit<F> {
    
    type Config = JsonConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        JsonConfig::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {

        let bs_ord = F::from(0x5c); // backslash
        let dq_ord = F::from(0x22); // double quote
        let ob_ord = F::from(0x7b); // open brace
        let cb_ord = F::from(0x7d); // close brace
        let special_chars = vec![bs_ord, dq_ord, ob_ord, cb_ord];
        let special_chars_column = vec![config.backslash, config.double_quote, config.open_brace, config.close_brace];
        let special_chars_inv_column = vec![config.backslash_inv, config.double_quote_inv, config.open_brace_inv, config.close_brace_inv];

        layouter.assign_region(
            || "Json circuit",
            |mut region| {

                let mut not_str = F::one();
                let mut level = F::zero();
                let mut level_inv = F::one();
                let mut str_esc = F::zero();
                let mut str_esc_prev = F::zero();

                let n = self.raw.len();

                for (idx, r) in self.raw.iter().enumerate() {

                    // println!("idx {:?} : raw = {:?}, \t not_str = {:?}", idx, r, not_str);

                    let _r = region.assign_advice(
                        || format!("raw input at idx = {}", idx),
                        config.raw,
                        idx,
                        || *r,
                    )?;

                    for (jdx, special_char) in special_chars.iter().enumerate() {

                        let _flag = _r.value().map(|x| {

                            if x == special_char {

                                if x == &dq_ord && str_esc_prev == F::zero() {
                                    not_str = F::one() - not_str;
                                } else if x == &ob_ord {
                                    level = level + not_str;
                                    level_inv = if level == F::zero() {F::one()} else {level.invert().unwrap()};
                                } else if x == &cb_ord {
                                    level = level - not_str;
                                    level_inv = if level == F::zero() {F::one()} else {level.invert().unwrap()};
                                } else if x == &bs_ord && str_esc_prev == F::zero() {
                                    str_esc = (F::one() - not_str) * F::one();
                                }

                                F::one()

                            } else {

                                F::zero()

                            }
                        });

                        let _inv = _r.value().map(|x| if x == special_char {F::one()} else {(*x - special_char).invert().unwrap()});
                        let _adv_flag = region.assign_advice(
                            || format!("flag for special char {}", jdx),
                            special_chars_column[jdx],
                            idx,
                            || _flag,
                        )?;
                        let _adv_inv = region.assign_advice(
                            || format!("inv for special char {}", jdx),
                            special_chars_inv_column[jdx],
                            idx,
                            || _inv,
                        )?;

                    }

                    // Handle str_esc step: 
                    // if str_esc_prev, escape is nullified: str_esc = str_esc * ( 1 - str_esc_prev )
                    // update str_esc_prev
                    str_esc = str_esc * (F::one() - str_esc_prev);
                    str_esc_prev = str_esc;

                    // Write state variables
                    let _not_str = region.assign_advice(
                        || format!("not_str at idx = {}", idx),
                        config.not_str,
                        idx,
                        || Value::known(not_str),
                    )?;

                    let _str_escaped = region.assign_advice(
                        || format!("str_escaped at idx = {}", idx),
                        config.str_escaped,
                        idx, 
                        || Value::known(str_esc)
                    )?;

                    let _level = region.assign_advice(
                        || format!("level at idx = {}", idx),
                        config.level,
                        idx,
                        || Value::known(level),
                    )?;

                    let _level_inv = region.assign_advice(
                        || format!("level_inv at idx = {}", idx),
                        config.level_inv,
                        idx,
                        || Value::known(level_inv),
                    )?;

                    // Set the selectors
                    config.json_all.enable(&mut region, idx)?;
                    if idx == 0 {
                        config.start_selector.enable(&mut region, idx)?;
                    } else if idx < n - 1 {
                        config.body_selector.enable(&mut region, idx)?;
                    } else {
                        config.end_selector.enable(&mut region, idx)?;
                    }

                }

                Ok(())
            }
        )

    }

}


#[cfg(test)]
mod test {

    use halo2_proofs::{
        arithmetic::Field, circuit::Value, dev::MockProver, halo2curves::bn256::Fr,
    };
    use rand::rngs::OsRng;
    use super::JsonCircuit;

    #[test]
    fn field_operations_test() {

        let test_str = String::from("abc");
        let char_arr = test_str.chars().collect::<Vec<char>>();
        println!("\nFirst Output: {:?}", char_arr.clone().into_iter().map(|x| format!("0x{:x}", x as u64)).collect::<Vec<String>>());

        let _arr = char_arr.into_iter().map(|x| Value::known(Fr::from(x as u64))).collect::<Vec<Value<Fr>>>();
        println!("\nSecond Output: {:?}", _arr[0]);

    }

    #[test]
    fn test_simple_json() {
        
        let k = 5;

        let test_json = String::from("{\"a\": 1, \"b\": 2}");
        let arr = test_json.chars().map(|x| Value::known(Fr::from(x as u64))).collect::<Vec<Value<Fr>>>();
        let circuit = JsonCircuit { raw: arr };

        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_json_escaped_chars() {
        
        let k = 5;

        let test_json = String::from("{\"a{}\": 1, \"b\": \"\\\"\"}");
        let arr = test_json.chars().map(|x| Value::known(Fr::from(x as u64))).collect::<Vec<Value<Fr>>>();
        let circuit = JsonCircuit { raw: arr };

        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
    }

    #[test]
    fn test_json_escaped_chars_2() {
        
        let k = 6;

        let test_json = String::from("{\"a{}\": \" \\\" { \\\" { \\\" \", \"b\": \"\\\"\"}");
        let arr = test_json.chars().map(|x| Value::known(Fr::from(x as u64))).collect::<Vec<Value<Fr>>>();
        let circuit = JsonCircuit { raw: arr };

        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
    }

    // Note that this does not check for valid key - value formats, which we will leave to a regex parser
    #[test]
    fn test_json_escaped_chars_3() {
        
        let k = 6;

        let test_json = String::from("{\"a{}\": \"1\" \"2\", \"b\": \"\\\"\"}");
        let arr = test_json.chars().map(|x| Value::known(Fr::from(x as u64))).collect::<Vec<Value<Fr>>>();
        let circuit = JsonCircuit { raw: arr };

        MockProver::run(k, &circuit, vec![]).unwrap().assert_satisfied();
    }

}