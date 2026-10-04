//! Check MLTL formulas and print cargo-style errors.
//!
//!     cargo run -p mltl-parse --example check -- 'p U[0,2] q U[0,3] r'
//!     cargo run -p mltl-parse --example check < formulas.txt   (one per line)
use std::io::{BufRead, IsTerminal};

fn check(text: &str, origin: &str, line: usize, color: bool) -> bool {
    match mltl_parse::parse_str(text) {
        Ok(f) => {
            println!("ok: {}", String::from_utf8_lossy(&mltl_parse::printer::print(&f)));
            true
        }
        Err(e) => {
            eprintln!("{}", e.render_at(text.as_bytes(), origin, line, color));
            false
        }
    }
}

fn main() {
    let color = std::io::stderr().is_terminal();
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut all_ok = true;
    if args.is_empty() {
        for (i, line) in std::io::stdin().lock().lines().enumerate() {
            let line = line.expect("read stdin");
            if !line.trim().is_empty() {
                all_ok &= check(&line, "<stdin>", i + 1, color);
            }
        }
    } else {
        for a in &args {
            all_ok &= check(a, "<input>", 1, color);
        }
    }
    std::process::exit(if all_ok { 0 } else { 1 });
}
