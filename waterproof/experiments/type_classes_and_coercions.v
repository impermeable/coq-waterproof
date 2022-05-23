(* Test coercion *)

Variable A B C : Type.
Variable AtoB : A -> B.
Coercion AtoB : A >-> B.

Class Op (T : Type) := my_op : T -> T -> C.
Variable op_A : Op A.
Variable op_B : Op B.
Instance inst_op_A : Op A := op_A.
Instance inst_op_B : Op B := op_B.

Variable a : A.
Variable b : B.

Check my_op a a.
Check my_op b b.
Fail Check my_op a b.
Check my_op b a.
(* Conclusion: type T is determined by first argument. *)