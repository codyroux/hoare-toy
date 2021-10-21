Require Import String ZArith Lia.
Require Export logic.


(* We need invariants to compute the WP *)
Definition inv_map := insn -> pred.

Search (Z -> Z -> bool).

Fixpoint wp (inv_map : inv_map) (insn : insn) (post : pred) : pred :=
  match insn with
  | Skip => post
  | x :== e => fun f => post (f [x --> eval_expr f e])
  | (i1 ; i2) => wp inv_map i1 (wp inv_map i2 post)
  | If e Then i1 Else i2 =>
    fun f =>
      if Zneq_bool (eval_expr f e) 0
      then wp inv_map i1 post f
      else wp inv_map i2 post f
  | (While e Do body Done) =>
    fun f =>
      let I := inv_map insn in
      (forall g, I g -> eval_expr g e = 0 -> post g)
      /\
      (* anything about eval_expr f e <> 0? *)
      I f
  end.

(* FIXME: this definition... *)
Definition inv_map_correct (inv_map : inv_map) : Prop :=
  forall e body,
    let I := inv_map (While e Do body Done) in
    hoare (fun f => eval_expr f e <> 0 /\ I f) body I.

Theorem wp_sound : forall inv_map post insn,
    inv_map_correct inv_map ->
    hoare (wp inv_map insn post) insn post.                         
Proof.
Admitted.



Theorem wp_complete : forall inv_map pre post insn,
    inv_map_correct inv_map ->
    hoare pre insn post ->
    forall f, pre f -> wp inv_map insn post f.
Proof.
Admitted.
