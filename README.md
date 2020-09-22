# Verified Solidity ABI Encoder/Decoder

This repository contains a specification, implementation, and verification (in Isabelle)
of the [Solidity ABI](https://solidity.readthedocs.io/en/latest/abi-spec.html) encoder and decoder.

The repository is structured as follows:

- ABI types and other basic notions: `AbiTypes.thy`
- Isabelle syntactic sugar for writing ABI types: `AbiTypesSyntax.thy`
- Constructs for error messages used in encoder and decoder implementations: `Ok.thy`
- Formal Solidity ABI encoding specification: `AbiEncodeSpec.thy`
- Encoder implementation: `AbiEncode.thy`
- Decoder implementation: `AbiDecode.thy`
- Encoder correctness theorems: `AbiEncodeCorrect.thy`
- Decoder correctness theorems: `AbiDecodeCorrect.thy`
- "Round-trip" theorems about decoding encoded results (and vice versa): `Inverses.thy`
- Isabelle files containing test inputs for encoder and decoder: `AbiTest.thy`