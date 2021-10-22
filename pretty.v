Require Import String ZArith Lia List.
Require Export lang.

Print List.nodup.

Search (list _ -> list _ -> list _).

Import ListNotations.

Fixpoint get_vars_expr (e : expr) : list string :=
  match e with
  | Var v => [v]
  | Const _ => []
  | Binop _ e1 e2 => get_vars_expr e1 ++ get_vars_expr e2
  end.

Fixpoint get_vars_dup (insn : insn) : list string :=
  match insn with
  | Skip => []
  | x :== e => x :: get_vars_expr e
  | (i1; i2) => get_vars_dup i1 ++ get_vars_dup i2
  | If e Then i1 Else i2 => get_vars_expr e ++ get_vars_dup i1 ++ get_vars_dup i2
  | While e Do body Done => get_vars_expr e ++ get_vars_dup body
  end.

Definition get_vars (insn : insn) : list string :=
  List.nodup string_dec (get_vars_dup insn).


Definition pos_get_digit (z : positive) : Z * Z :=
  Z.pos_div_eucl z 10.


Fixpoint pos_to_digits (z : positive)(digits : list Z) (gas : nat) :=
  match gas with
  | 0%nat => []
  | S gaz =>
    let '(div, rem) := pos_get_digit z in
    if div =? 0 then
      rem::digits
    else
      let div := Z.to_pos div in
      pos_to_digits div (rem::digits) gaz
  end.

Print Z. Print Module String.
Search (Z -> nat).

Definition digit_to_string (z : Z) : string :=
  if (z =? 0) then "0"
  else if (z =? 1) then "1"
       else if (z =? 2) then "2"
            else if (z =? 3) then "3"
                 else if (z =? 4) then "4"
                      else if (z =? 5) then "5"
                           else if (z =? 6) then "6"
                                else if (z =? 7) then "7"
                                     else if (z =? 8) then "8"
                                          else if (z =? 9) then "9"
                                               else "".

Definition Z_to_string (z : Z) : string :=
  match z with
  | Z0 => "0"
  | Zpos p => String.concat "" (List.map digit_to_string (pos_to_digits p [] (Z.abs_nat z)))
  | Zneg p => "-" ++ String.concat "" (List.map digit_to_string (pos_to_digits p [] (Z.abs_nat z)))
  end.

Eval compute in Z_to_string 123456.

Eval compute in Z_to_string (-256)%Z.

Eval compute in Z_to_string (-010)%Z.

Check Binop.
Print binop.

Definition binop_to_string (b : binop) : string :=
  match b with
  | Add => " + "
  | Sub => " - "
  | Leq => " <= "
  end.

Fixpoint pp_expr (e : expr) : string :=
  match e with
  | Var v => v
  | Const c => Z_to_string c
  | Binop b e1 e2 =>
    "(" ++ pp_expr e1 ++ binop_to_string b ++ pp_expr e2 ++ ")"
  end.

Eval compute in pp_expr (3 + "x" - 2).

Print Module String.

Require Import Ascii.

Print string.

Definition newline := String "010"%char EmptyString.

Definition pp_newline (s : string) : string :=
  s ++ newline.

Eval compute in pp_newline "foobar".


Fixpoint pp_insn_aux (i : insn) : string :=
  match i with
  | Skip => ""
  | x :== e => x ++ " = " ++ pp_expr e
  | (i1; i2) =>
    let s1 := pp_insn_aux i1 ++ ";" in
    let s2 := pp_insn_aux i2 in
    (pp_newline s1) ++ s2
  | If e Then i1 Else i2 =>
    let s_cond := pp_expr e in
    let s1 := pp_insn_aux i1 ++ ";" in
    let s2 := pp_insn_aux i2 ++ ";" in
    (pp_newline ("if (" ++ s_cond ++ ")"))
      ++
      (pp_newline ("{ " ++ s1 ++ " }"))
      ++
      ("else { " ++ s2 ++ "}")
  | While e Do body Done =>
    let s_cond := pp_expr e in
    let s_body := pp_insn_aux body ++ ";" in
    (pp_newline ("while (" ++ s_cond ++ ")"))
      ++
      ("{ " ++ s_body ++ " }")
  end.

Definition pp_insn i := pp_insn_aux i ++ ";".

Eval compute in pp_insn (While (0 <= "x") Do ("x" :== "x" - 1) Done).
