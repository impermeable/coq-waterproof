# Waterproof Change Log Tag 1.1.0

- Added and updated theory files.
- Reorganized automation libraries.
- Added goal wrappers that force user to write sentences that make proofscript more readable.
- Support chains of (in)equalities for `=`, `<` and `<=` in naturals and reals.
- Fixed issues with several tactics, including `Take ...`.
- Rephrased multiple tactics like `Obtain ... according to ..., ...`.
- For propositions, have user specify types rather than labels in tactics. Labeling is now optional.
- Added some shielding for use of automation, e.g. statements starting with quantifiers cannot be proved automatically.
