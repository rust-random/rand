extern crate version_check;

fn main() {
    if version_check::is_min_version("1.26.0").expect("couldn't query version info from rustc").0 {
        println!("cargo:rustc-cfg=stable_i128");
    }
}
