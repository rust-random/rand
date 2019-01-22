'use strict';

const rand_wasm_bindgen_test = require('./rand_wasm_bindgen_test');

console.log(rand_wasm_bindgen_test.generate_from_entropy());
console.log(rand_wasm_bindgen_test.generate_from_os_rand());
console.log(rand_wasm_bindgen_test.generate_from_seed());
