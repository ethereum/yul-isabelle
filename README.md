# Yul-Isabelle: Executable Formal Semantics of Yul

This repository contains an implementation of a semantics for the
[Yul](https://docs.soliditylang.org/en/v0.8.2/yul.html) laguage using
the [Isabelle/HOL](https://isabelle.in.tum.de/) proof assistant.
It is compatible with Isabelle2021.

Design goals are to create a maintainable formal semantics of Yul -
including a reference interpreter - suitable for use in verifying
Solidity compiler transformations.

The Yul language is designed to be integrated with a machine language,
such that Yul captures control-flow and variable-assignment, and
the machine language's primitives capture the remaining functionality.
Such a combination is called a *Yul Dialect*. In this repository we
focus on the *Yul/EVM Dialect*.

The repository is organized as follows:

- `Yul`: Implementation of Yul syntax and control-flow semantics

  - `YulSyntax`: Yul semantics AST data structure

  - `YulSemanticsSingleStep`: executable reference interpreter for Yul

  - `YulDialect`: Useful primitives for defining dialects of Yul
  
  - `YulSemantics`: inductive semantics for Yul; currently incomplete

- `Word_Lib`: A copy of the ["Word_Lib" entry](https://www.isa-afp.org/entries/Word_Lib.html) from the Isabelle Archive of Formal Proofs
  (as of Isabelle2021, several useful operations on Isabelle machine words have been
  moved out of the standard library and into this entry)

- `EVM`: an implementation of a substantial subset of the [EVM virtual machine](https://ethereum.github.io/yellowpaper/paper.pdf)
  for use in defining the Yul/EVM dialect.
  Based on [LLL tests](https://github.com/ethereum/tests/blob/develop/src/VMTestsFiller) from Solidity.

  - `MiniEvm`: An implementation of a large subset of EVM operations. Currently does not model gas accounting or cross-contract calls. Used in the EVM dialect.

  - `LowLevelEvm`: An implementation of a datatype for EVM bytecodes, currently incomplete

  - `GlobalEvm`: An attempt at modeling global Ethereum state and cross-contract behaviors, currently incomplete

- `EvmTests`: Tests for the EVM implementation contained in `EVM`

- `Keccak`: Isabelle implementation of Keccak256, drawn from [eth-isabelle](https://github.com/pirapira/eth-isabelle)

- `Dialects`: Instantiations of Yul to different dialects; most importantly, EVM

  - `EvmDialect`: the Yul/EVM dialect

- `YulTests`: Tests for the Yul interpreter, including the EVM dialect