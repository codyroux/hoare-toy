Require Import String ZArith Lia.
Require Import lang.
Require Import logic.
Require Import pretty.

Fixpoint fib (n : nat) :=
  (match n with
  | 0 => 0
  | S k =>
    match k with
    | 0 => 1
    | S l => fib k + fib l
    end
  end)%nat.


Definition fib_imp : insn :=
  ("x" :== 0;
  "y" :== 1;
  While (1 <= "input") Do
        ("sum" :== "x" + "y";
        "x" :== "y";
        "y" :== "sum";
        "input" :== "input" - 1)
        Done;
  "output" :== "sum").

Search (nat -> Z).

(* Idea: automatically prove a correspondance between tail-recursive
   function and while loops. *)
Theorem fib_imp_correct : forall n : nat,
    hoare (fun f => f "input" = Z.of_nat n)
          fib_imp
          (fun g => g "output" = Z.of_nat (fib n)).
Proof.
  intros.
Abort.
