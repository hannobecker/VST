(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Function calling conventions and other conventions regarding the use of
    machine registers and stack slots. *)

Require Import compcert.lib.Coqlib.
Require Import VST.ccc26x86.Decidableplus.
Require Import compcert.common.AST.
Require Import compcert.common.Events.
Require Import VST.ccc26x86.Locations.

(** * Classification of machine registers *)

(** Machine registers (type [mreg] in module [Locations]) are divided in
  the following groups:
- Callee-save registers, whose value is preserved across a function call.
- Caller-save registers that can be modified during a function call.

  We follow the x86-32 application binary interface (ABI) in our choice
  of callee- and caller-save registers.
*)

Definition is_callee_save (r: mreg) : bool :=
  match r with
  | AX | CX | DX => false
  | BX | SI | DI | BP => true
  | X0 | X1 | X2 | X3 | X4 | X5 | X6 | X7 => false
  | FP0 => false
  end.

Definition int_caller_save_regs := AX :: CX :: DX :: nil.

Definition float_caller_save_regs := X0 :: X1 :: X2 :: X3 :: X4 :: X5 :: X6 :: X7 :: nil.

Definition int_callee_save_regs := BX :: SI :: DI :: BP :: nil.

Definition float_callee_save_regs : list mreg := nil.

Definition destroyed_at_call :=
  List.filter (fun r => negb (is_callee_save r)) all_mregs.

Definition dummy_int_reg := AX.     (**r Used in [Regalloc]. *)
Definition dummy_float_reg := X0.   (**r Used in [Regalloc]. *)

(** * Function calling conventions *)

(** The functions in this section determine the locations (machine registers
  and stack slots) used to communicate arguments and results between the
  caller and the callee during function calls.  These locations are functions
  of the signature of the function and of the call instruction.
  Agreement between the caller and the callee on the locations to use
  is guaranteed by our dynamic semantics for Cminor and RTL, which demand
  that the signature of the call instruction is identical to that of the
  called function.

  Calling conventions are largely arbitrary: they must respect the properties
  proved in this section (such as no overlapping between the locations
  of function arguments), but this leaves much liberty in choosing actual
  locations.  To ensure binary interoperability of code generated by our
  compiler with libraries compiled by another compiler, we
  implement the standard x86 conventions. *)

(** ** Location of function result *)

(** The result value of a function is passed back to the caller in
  registers [AX] or [DX:AX] or [FP0], depending on the type of the returned value.
  We treat a function without result as a function with one integer result. *)

Definition loc_result (s: signature) : rpair mreg :=
  match s.(sig_res) with
  | None => One AX
  | Some (Tint | Tany32) => One AX
  | Some (Tfloat | Tsingle) => One FP0
  | Some Tany64 => One X0
  | Some Tlong => Twolong DX AX
  end.

(** The result registers have types compatible with that given in the signature. *)

Lemma loc_result_type:
  forall sig,
  subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.
Proof.
  intros. unfold proj_sig_res, loc_result. destruct (sig_res sig) as [[]|]; auto.
Qed.

(** The result locations are caller-save registers *)

Lemma loc_result_caller_save:
  forall (s: signature),
  forall_rpair (fun r => is_callee_save r = false) (loc_result s).
Proof.
  intros.
  unfold loc_result. destruct (sig_res s) as [[]|]; simpl; auto.
Qed.

(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)

Lemma loc_result_pair:
  forall sg,
  match loc_result sg with
  | One _ => True
  | Twolong r1 r2 => r1 <> r2 /\ sg.(sig_res) = Some Tlong /\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
  end.
Proof.
  intros; unfold loc_result; destruct (sig_res sg) as [[]|]; auto. intuition congruence.
Qed.

(** ** Location of function arguments *)

(** All arguments are passed on stack. (Snif.) *)

Fixpoint loc_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : list (rpair loc) :=
  match tyl with
  | nil => nil
  | ty :: tys =>
      match ty with
      | Tlong => Twolong (S Outgoing (ofs + 1) Tint) (S Outgoing ofs Tint)
      | _     => One (S Outgoing ofs ty)
      end
      :: loc_arguments_rec tys (ofs + typesize ty)
  end.

(** [loc_arguments s] returns the list of locations where to store arguments
  when calling a function with signature [s].  *)

Definition loc_arguments (s: signature) : list (rpair loc) :=
  loc_arguments_rec s.(sig_args) 0.

(** [size_arguments s] returns the number of [Outgoing] slots used
  to call a function with signature [s]. *)

Fixpoint size_arguments_rec
    (tyl: list typ) (ofs: Z) {struct tyl} : Z :=
  match tyl with
  | nil => ofs
  | ty :: tys => size_arguments_rec tys (ofs + typesize ty)
  end.

Definition size_arguments (s: signature) : Z :=
  size_arguments_rec s.(sig_args) 0.

(** Argument locations are either caller-save registers or [Outgoing]
  stack slots at nonnegative offsets. *)

Definition loc_argument_acceptable (l: loc) : Prop :=
  match l with
  | R r => is_callee_save r = false
  | S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
  | _ => False
  end.

Definition loc_argument_charact (ofs: Z) (l: loc) : Prop :=
  match l with
  | S Outgoing ofs' ty => ofs' >= ofs /\ typealign ty = 1
  | _ => False
  end.

Remark loc_arguments_rec_charact:
  forall tyl ofs p,
  In p (loc_arguments_rec tyl ofs) -> forall_rpair (loc_argument_charact ofs) p.
Proof.
  assert (X: forall ofs1 ofs2 l, loc_argument_charact ofs2 l -> ofs1 <= ofs2 -> loc_argument_charact ofs1 l).
  { destruct l; simpl; intros; auto. destruct sl; auto. intuition omega. }
  induction tyl as [ | ty tyl]; simpl loc_arguments_rec; intros.
- contradiction.
- destruct H.
+ destruct ty; subst p; simpl; omega.
+ apply IHtyl in H. generalize (typesize_pos ty); intros. destruct p; simpl in *.
* eapply X; eauto; omega.
* destruct H; split; eapply X; eauto; omega.
Qed.

Lemma loc_arguments_acceptable:
  forall (s: signature) (p: rpair loc),
  In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.
Proof.
  unfold loc_arguments; intros.
  exploit loc_arguments_rec_charact; eauto.
  assert (X: forall l, loc_argument_charact 0 l -> loc_argument_acceptable l).
  { destruct l as [r | [] ofs ty]; simpl; intuition auto. rewrite H2; apply Z.divide_1_l. }
  destruct p; simpl; intuition auto.
Qed.

Hint Resolve loc_arguments_acceptable: locs.

(** The offsets of [Outgoing] arguments are below [size_arguments s]. *)

Remark size_arguments_rec_above:
  forall tyl ofs0, ofs0 <= size_arguments_rec tyl ofs0.
Proof.
  induction tyl; simpl; intros.
  omega.
  apply Zle_trans with (ofs0 + typesize a); auto.
  generalize (typesize_pos a); omega.
Qed.

Lemma size_arguments_above:
  forall s, size_arguments s >= 0.
Proof.
  intros; unfold size_arguments. apply Zle_ge.
  apply size_arguments_rec_above.
Qed.

Lemma loc_arguments_bounded:
  forall (s: signature) (ofs: Z) (ty: typ),
  In (S Outgoing ofs ty) (regs_of_rpairs (loc_arguments s)) ->
  ofs + typesize ty <= size_arguments s.
Proof.
  intros until ty. unfold loc_arguments, size_arguments. generalize (sig_args s) 0.
  induction l as [ | t l]; simpl; intros x IN.
- contradiction.
- rewrite in_app_iff in IN; destruct IN as [IN|IN].
+ apply Zle_trans with (x + typesize t); [|apply size_arguments_rec_above].
  Ltac decomp :=
  match goal with
  | [ H: _ \/ _ |- _ ] => destruct H; decomp
  | [ H: S _ _ _ = S _ _ _ |- _ ] => inv H
  | [ H: False |- _ ] => contradiction
  end.
  destruct t; simpl in IN; decomp; simpl; omega.
+ apply IHl; auto.
Qed.

Lemma loc_arguments_main:
  loc_arguments signature_main = nil.
Proof.
  reflexivity.
Qed.
