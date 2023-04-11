* [x] Write a file with all kinds of examples for automation, with things that should and shouldn't work.
* Expressions with Rmax and Rabs initially provided very good examples, because lra and nra cannot look inside of them. However, at the bottom of this file certain tactics are used to the hint databases, which makes these apparently quite doable.
* [ ] What should be the cost of Lra? nra? Do we want to use  them at all?
* [ ] At the bottom of the file, there are ways to deal with Rmax and Rabs for lra. How good are they? Can they handle multiple Rmax in an inequality for instance?
* [x] Have we understood the 'cost' in the automation wrong?: does it relate to the search depth?
* [ ] Clean up our automation tactics:
  * [ ] Seems we are not using `global_use_all_databases` option for instance.
  * [x] Add a debug possibility in our own tactics
* [x] Use debug in ltac2
* [ ] Make info_auto information available to coq-waterproof
  * [ ] For instance to make sure that a lemma is actually used when writing "By ... it holds that ()."
  * [ ] Or, to give the user a hint for an intermediate step (this would be very nice but is possibly very difficult).
* [ ] Make debug information available to coq-waterproof
* [ ] Write a plugin?