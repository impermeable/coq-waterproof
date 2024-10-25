# Change log for the coq-waterproof library

## Version 2.2.0+8.17

- Allow for standard math notation
- No longer automatically replace terms introduced by choose in the goal
- Add bullets and curly brackets to wrappers
- Update the induction tactic, so that the variable needs to be introduced in the induction step
- Allow for obtaining multiple variables
- Test warning and error messages
- Update documentation and add developer documentation
- Simplify the build proces
- Create a devcontainer
- Warn on unexpected variable names by comparing to binder names
- Refactor the ffi
- Change expand definition tactic so it unfolds in all statements
- Add possibility to postpone proofs
- Quickfix for using Qed as variable name
- Allow for choosing blanks
- Add custom version of the specialize tactic
- Allow for boolean statements in tactics

## Version 2.1.1+8.17

- Compatibility with earlier OCaml compilers
- Fixes for the strong induction tactic

## Version 2.1.0+8.17

- Improve the `Either` tactic: now proves and destructs ordinary 'ors' when the goal is a proposition
- Improve some mathematical definitions
- Add vernacular for debugging automation

## Version 2.0.2+8.17

- Improve errors and warnings
- Rework expanding definitions
- Deal better with Rabs, Rmax, Rmin

## Version 2.0.1+8.17

- Build the plugin with dune

## Version 2.0.0

- Converted coq library to coq plugin
- Automation procedures are now handled internally in the plugin, so that they can be customized and so that one can check the use of certain lemmas within the automation

## Version 1.2.4

- Added and updated theory files.
- Improved notation for (in)equality chains, e.g. (& a < b <= c = d).
- Bug fixes.

## Version 1.1.2

- Added and updated theory files.
- Reorganized automation libraries.
- Added goal wrappers that force user to write sentences that make proofscript more readable.
- Support chains of (in)equalities for `=`, `<` and `<=` in naturals and reals.
- Fixed issues with several tactics, including `Take ...`.
- Rephrased multiple tactics like `Obtain ... according to ..., ...`.
- For propositions, have user specify types rather than labels in tactics. Labeling is now optional.
- Added some shielding for use of automation, e.g. statements starting with quantifiers cannot be proved automatically.

## Version 1.0.0

- Ported the original library written in ltac to Ltac2.
