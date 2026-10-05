// Prints the verdicts R2U2 emits at each time step: "step N: spec:time,T ...".
use std::env;
fn main() {
    let a: Vec<String> = env::args().collect();
    let spec = std::fs::read(&a[1]).unwrap();
    let mut m = r2u2_core::get_monitor(&spec);
    for (n, row) in a[2].split(';').enumerate() {
        for (i, c) in row.chars().enumerate() { r2u2_core::load_bool_signal(&mut m, i, c == '1'); }
        r2u2_core::monitor_step(&mut m);
        let outs: Vec<String> = r2u2_core::get_output_buffer(&m).iter()
            .map(|o| format!("{}:{},{}", o.spec_num, o.verdict.time, if o.verdict.truth {"T"} else {"F"})).collect();
        println!("step {}: {}", n, outs.join(" "));
    }
}
