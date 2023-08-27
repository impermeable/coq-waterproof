# Change log for the coq-waterproof library

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
