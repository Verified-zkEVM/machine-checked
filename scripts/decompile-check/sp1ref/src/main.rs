//! Run SP1 guests on SP1's executor, on the five test inputs of the check.
//!
//!     sp1ref GUEST.elf ...
//!
//! For each guest and input it prints the public values, the exit code and the number of
//! instructions executed, or the executor's error. `check.py sp1-reference` compares these
//! with what `sp1run.py` says of the same guest.

use sp1_sdk::{blocking::{Prover, ProverClient}, Elf, SP1Stdin};

fn lcg(seed: u64, n: usize) -> Vec<u8> {
    let mut x = seed;
    (0..n)
        .map(|_| {
            x = x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (x >> 56) as u8
        })
        .collect()
}

fn main() {
    let inputs = [vec![], lcg(1, 16), lcg(2, 64), lcg(3, 256), vec![0xff; 64]];
    let client = ProverClient::builder().cpu().build();
    for path in std::env::args().skip(1) {
        let bytes = std::fs::read(&path).expect("cannot read the guest");
        println!("# {path}");
        for input in &inputs {
            // the two hint vectors of an input: its bytes, and its bytes backwards
            let mut stdin = SP1Stdin::new();
            stdin.write_slice(input);
            stdin.write_slice(&input.iter().rev().copied().collect::<Vec<u8>>());
            match client.execute(Elf::from(bytes.clone()), stdin).run() {
                Ok((public, report)) => println!(
                    "public={} exit={} instructions={}",
                    hex::encode(public.as_slice()),
                    report.exit_code,
                    report.total_instruction_count()
                ),
                Err(e) => println!("error: {e}"),
            }
        }
    }
}
