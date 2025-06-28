# Developer instructions

## Recommended setup

Our recommended setup for working on the library is by using vscode on Linux, MacOS, or WSL, with
the coq-lsp and ocaml extensions. We will now describe more extensively how to achieve this setup.

### Installation of opam

A more extensive description can be found [here](https://ocaml.org/docs/installing-ocaml).
This is a short description.

On some versions of Linux and WSL, you can install opam with
```
apt-get install opam
```
On MacOs, you can either use homebrew
```
brew install gpatch
brew install opam
```
or macports
```
port install opam
```

### Creating the desired opam environment: simplified version
When we develop, we need to be aware of the version of Coq we develop for.
Most development is done based off the main branch, and then the following setup will suffice.

```
opam init
eval $(opam env)
opam install coq-lsp.0.2.0+8.17
opam install ocaml-lsp-server
```
replacing 8.17 with the desired version of Coq, or more generally, replacing
0.2.0+8.17 by the desired version of coq-lsp.

### Creating the desired opam environment: advanced version for supporting multiple versions of Coq

When we bring changes into different versions of Coq (for instance for the branches 8.18, 8.19...)
it is convenient to have multiple opam environement, i.e. switches, available. If you prefer to start
with such a setup anyway, you can run
```
opam init --bare
```
Regardless of how you initialized opam, you can now add a new switch with
```
opam switch create your_preferred_switch_name ocaml-base-compiler.4.14.1
```
Next you can install the background libraries again
```
opam install coq-lsp.0.2.0+8.17
opam install ocaml-lsp-server
```
again replacing 8.17 with the desired version of Coq

### Caveat: locally compiling the coq-master branch

The above only works partially when checking work for `coq-master`,  which is a very important
branch for us because it is checked in Coq's CI. To just check locally whether the code works on the
`coq-master` branch, we can setup
```
opam switch create your_preferred_switch_name ocaml-base-compiler.4.14.1
```
Now, we need to add a remote repository to get the development version of coq from.
```
opam repo add coq-dev https://coq.inria.fr/opam/core-dev
opam update
```
Now we can install
```
opam install coq.dev
```

## Building with dune

Our go-to way for compiling `coq-waterproof` while working on the library is by using dune. To do so, from the project's
root (i.e. inside the directory `...some-path.../coq-waterproof/`), run
```
dune build -p coq-waterproof
```
To then install the library so it is available from other projects, you can run
```
dune install -p coq-waterproof
```

## Building with opam

The above method does not pin `coq-waterproof` to the local version in the working
directory. Instead, one can run, from the root directory,
```
opam install .
```
and `coq-waterproof` _will_ be pinned to the local version, and will
be installed (in the current opam switch).

## Warning

When importing Waterproof in a .v file when using coq-lsp, we standard get the following warning

```
Serlib plugin: coq-waterproof.plugin is not available: serlib support is missing. Incremental checking for commands in this plugin will be impacted.
```

This is not a problem.

## Testing

We aim to test every feature that we implement. Currently we test almost
all functionality present in `.v` files. Note for instance that tactics
such as `Choose`, `Assume`, both have a file that defines them, and a file
that tests them. The tests are run automatically when compiling the library, i.e.
when running
```
dune build -p coq-waterproof
```

## Running external tests

If one has symlink to a folder called `waterproof-exercises` 
in the project root (i.e. in `coq-waterproof`), one can test coq-waterproof against all the files
(typically exercise sheets) in `waterproof-exercises` by executing

```
dune build -p coq-waterproof @runtest
```

## Setting up VSCode

If you use VSCode, we recommend installing the [OCaml Platform](https://marketplace.visualstudio.com/items?itemName=ocamllabs.ocaml-platform) and [Coq LSP](https://marketplace.visualstudio.com/items?itemName=ejgallego.coq-lsp) plugins.

## Making Ocaml functions available from Ltac2: Using the foreign function interface (ffi)

One can make Ocaml functions available for use in Ltac2 by using the
foreign function interface (ffi). For now, we gather all such
definitions in `Wp_ffi.ml`.

Suppose one has an Ocaml function `f : a -> b -> c -> d` where `a, b, c, d` are types, and one would like to make this function available as an Ltac2 tactic.

### Make a tactic

First of all, only tactics can pass the ffi, so one needs to convert `f` into
something that outputs a tactic. An element of type `'a` can be converted into an `'a`-valued tactic, ie.e. an element of type `'a tactic` by using `tclUNIT`:

Consider this example:
```
let my_unit_tactic : unit tactic = tclUNIT ()
```

```
let my_bool_tactic : bool tactic = tclUNIT true
```

Hence, we can convert `f` into something that outputs a tactic by

```
let my_f_tactic : a -> b -> c -> d tactic =
  fun input_a input_b input_c -> tclUNIT (f input_a input_b input_c)
```

### Make a `valexpr` tactic

Datatypes in Ocaml and in Ltac2 need to be translated to each other
by using an intermediate datatype: namely `valexpr`. This also means that
only `valexpr`-valued tactics can pass the ffi.
Luckily, for many types there are already conversion functions available from
and to `valexpr`, such as `of_bool`, `to_bool` and `of_unit`, `to_unit`.
In general, these conversions are captured in elements of the type `'a repr`:
an element `c` of `'a repr` has a conversion `repr_to c : valexpr -> 'a` and
a conversion `repr_of c : 'a -> valexpr`. For more information, one can look
at Coq's `tac2ffi.ml` file.

We can then use the strategy from the previous section to make a valexpr tactic.
```
let my_valexpr_tactic_from_unit : valexpr tactic = tclUNIT (of_unit ())
```
It is common to use the `@@` operator to put everything that comes after it
in parentheses, so one could also write
```
let my_valexpr_tactic_from_unit : valexpr tactic = tclUNIT @@ of_unit ()
```
Similarly, here is a `valexpr` tactic created from a `bool`
```
let my_valexpr_tactic_from_bool : valexpr tactic = tclUNIT @@ of_bool ()
```

### Make the function available for the ffi

Considering an example of a function `f : a -> b -> c -> d`, and given
`a_repr : a repr`, `b_repr : b repr`, `c_repr : c repr`, `d_repr : d repr`, we can
make this function available for the ffi by

```
let () = define3 "my_f_external" a_repr b_repr c_repr @@
  fun input_a, input_b, input_c ->
    tclUNIT (repr_of d (f input_a input_b input_c))
```

The `3` is chosen because `f` has `3` inputs.

Note that with some monad magic, the same definition can also be
achieved by
```
let () = define3 "my_f_external" a_repr b_repr c_repr @@
  fun input_a input_b input_c ->
    tclUNIT @@ f input_a input_b input_c >>= fun z -> tclUNIT @@ repr_of d z
```
Here "my_f_external" is the name by which you can refer to this function
from Ltac2. Any name can be chosen, and it won't be the name that you use
to call the function from Ltac2. Representations for many different datatypes
can be found in Coq's `tac2ffi.ml`. For many datatypes, the respresentation
of that datatype is called the same: `bool` is for instance the name for `bool repr`, so that the following would be valid code

```
let () = define1 "my_bool_tactic" bool @@
  fun input -> tclUNIT input >>= fun z -> tclUNIT @@ of_bool z
```
or yet another option
```
let () = define1 "my_bool_tactic" bool @@
  fun input -> tclUNIT input >>= fun z -> tclUNIT @@ repr_of bool z
```

Note that in Coq v8.19, a new file `tac2externals.ml` was created, which
can be used to handle a lot of the above issues.

### Make the function available from Ltac2

From a `.v` file, one can simply load
```
Require Import Waterproof.Waterproof.
```
and then define (in Coq v8.17) (given the caveat below)
```
Ltac2 @ external my_f_in_ltac2 : a_ltac2 -> b_ltac2 -> c_ltac2 -> d_ltac2 := "coq-waterproof" "my_f_external".
```
where `a_ltac2`, ... `d_ltac2` are the corresponding types on the
Ltac2 side of the types `a`, ..., `d`. The caveat is that there aren't always
corresponding types on the Ltac2 side of Ocaml types.

Note that the syntax is a bit different in different versions of Coq.
Please see the code for examples.
