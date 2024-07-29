// An external test assures that the usage of a private trait by Rng::gen_index
// does not cause issues with intended usages.

use rand::Rng;

#[test]
fn sample_index() {
    let mut rng = rand::rngs::mock::StepRng::new(0, 579682777108047081);
    assert!(rng.gen_index(..4) < 4);
    assert_eq!(rng.gen_index(..=0), 0);
    assert_eq!(rng.gen_index(0..1), 0);
    assert!(rng.gen_index(0..=9) < 10);
}
