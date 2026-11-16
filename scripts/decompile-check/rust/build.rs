// A bare program is linked by `bare.x`; an SP1 guest by SP1's own script.
fn main() {
    if std::env::var("CARGO_CFG_TARGET_OS").as_deref() == Ok("none") {
        let dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
        println!("cargo:rustc-link-arg-bins=-T{dir}/bare.x");
        println!("cargo:rustc-link-arg-bins=--no-relax");
        println!("cargo:rerun-if-changed=bare.x");
    }
}
