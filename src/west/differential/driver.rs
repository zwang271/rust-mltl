//! Differential-test driver for the verified WEST: reads prefix formulas
//! (see gen.py) from stdin and prints, per formula, `WEST_reg` and
//! `simp_pad_WEST_reg` in the format of Isabelle's `show` on lists.
use mltl_core::mltl::Mltl;
use std::io::{self, BufRead, Write};
use west::algorithms::WestBit;
use west::exec::{simp_pad_WEST_reg, WEST_reg, ExecRegex};

fn parse(t: &[String], i: &mut usize) -> Mltl<usize> {
    let tok = t[*i].clone();
    *i += 1;
    match tok.as_str() {
        "T" => return Mltl::True,
        "F" => return Mltl::False,
        "(" => {}
        _ => panic!("bad token {tok}"),
    }
    let op = t[*i].clone();
    *i += 1;
    let num = |i: &mut usize| { let x: usize = t[*i].parse().unwrap(); *i += 1; x };
    let f = match op.as_str() {
        "P" => Mltl::Prop(num(i)),
        "N" => Mltl::Not(Box::new(parse(t, i))),
        "A" => { let x = parse(t, i); Mltl::And(Box::new(x), Box::new(parse(t, i))) }
        "O" => { let x = parse(t, i); Mltl::Or(Box::new(x), Box::new(parse(t, i))) }
        "Fu" => { let a = num(i); let b = num(i); Mltl::Future(a, b, Box::new(parse(t, i))) }
        "G" => { let a = num(i); let b = num(i); Mltl::Global(a, b, Box::new(parse(t, i))) }
        "U" => { let x = parse(t, i); let a = num(i); let b = num(i); Mltl::Until(Box::new(x), a, b, Box::new(parse(t, i))) }
        "R" => { let x = parse(t, i); let a = num(i); let b = num(i); Mltl::Release(Box::new(x), a, b, Box::new(parse(t, i))) }
        _ => panic!("bad op {op}"),
    };
    assert_eq!(t[*i], ")");
    *i += 1;
    f
}

fn show(r: &ExecRegex) -> String {
    let bit = |b: &WestBit| match b { WestBit::Zero => "Zero", WestBit::One => "One", WestBit::S => "S" };
    let list = |xs: Vec<String>| format!("[{}]", xs.join(","));
    list(r.iter().map(|t| list(t.iter().map(|s| list(s.iter().map(|b| bit(b).to_string()).collect())).collect())).collect())
}

fn main() {
    let out = io::stdout();
    let mut out = out.lock();
    for line in io::stdin().lock().lines() {
        let line = line.unwrap();
        if line.trim().is_empty() { continue; }
        let toks: Vec<String> = line.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect();
        let f = parse(&toks, &mut 0);
        writeln!(out, "{}", show(&WEST_reg(&f))).unwrap();
        writeln!(out, "{}", show(&simp_pad_WEST_reg(&f))).unwrap();
    }
}
