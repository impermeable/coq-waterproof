This directory contains files that the user can import
to customize the set of databases used.
Each file only contains a command that changes a global variable.

For example, to add the `General` database to the set of databases
used by automation, one can use:
```coq
Require Import Waterproof.load_database.General.
```