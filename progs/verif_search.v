
Require Import VST.floyd.proofauto.
Require Import VST.progs.search.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
From mathcomp.ssreflect Require Import ssreflect.

Definition Znth_opt { X : Type } (n : Z) (lst : list X) : option X :=
  Znth n (map Some lst) None.

Section SearchSpec.
  Variable X : Type.

  (* Search for an element within a list.
   *
   * Return:
   * - The 0-based index of the first match on success,
   * - None otherwise.
   *)
  Variable search : X -> list X -> option Z.

  Definition search_spec0 : Prop :=
    forall (target : X) (lst : list X) (i : Z),
    search target lst = Some i <-> (
      0 <= i < Zlength lst          /\
      Znth_opt i lst = Some target /\
      forall (j : Z), 0 <= j < i -> Znth_opt j lst <> Some target ).

  Lemma search_none :
    search_spec0 -> forall (target : X) (lst : list X),
      ( ( forall (i : Z), 0 <= i < Zlength lst -> Znth_opt i lst <> Some target )
        -> search target lst = None ).
  Proof.
    move => H_spec target lst H_asm.
    destruct (search target lst) as [ i | _ ] eqn:H_eq; last done.
    (* Need to discharge `search target lst = Some i` *)
    move : H_eq.
    move /H_spec => [] H_i [] H_match.
    exfalso.
    apply (H_asm i); assumption.
  Qed.

End SearchSpec.

Module Type Ty.
  Parameter X : Type.
End Ty.

Module ZTy <: Ty.
  Definition X : Type := Z.
End ZTy.

Module Type SearchImplementation ( XTy : Ty ).
  Export XTy.
  Parameter search : X -> list X -> option Z.
  Parameter search_spec : search_spec0 X search.
End SearchImplementation.

Module C_search_verify (Imp : SearchImplementation ZTy).
  Import Imp.

  Definition Csearch_spec : ident * funspec :=
    DECLARE _search
      WITH arr: val, sh: share, contents: list Z, length: Z, target: Z
      PRE [ _arr OF (tptr tint), _length OF tint, _target OF tint ]
        PROP (readable_share sh;
              (* Make sure abstract integers are within
                 the representable range of machine integers *)
              0 <= length <= Int.max_signed;
              repable_signed target;
              Forall repable_signed contents)
        LOCAL ( temp _arr    arr;
                temp _length (Vint (Int.repr length));
                temp _target (Vint (Int.repr target)) )
        SEP   ( (* length represents the contents of the
                   length `length` array starting at `array`. *)
                data_at sh (tarray tint length)
                           (map Vint (map Int.repr contents))
                           arr )
      POST [ tint ]
        PROP  (True)
        LOCAL ( temp ret_temp (
                       (* Convert list index to pointer *)
                       match (search target contents) with
                       | None (* Nothing found, expect NULL pointe *)
                           => Vint (Int.repr (-1%Z))
                       | Some idx%Z
                           => Vint (Int.repr idx)
                       end ) )
        SEP   ( (* Data hasn't been modified or freed *)
                data_at sh (tarray tint length)
                           (map Vint (map Int.repr contents))
                           arr ).

  Definition Gprog := ltac:(with_library prog [Csearch_spec]).

  Lemma body_search_alt: semax_body Vprog Gprog f_search_alt Csearch_spec.
  Proof.
    pose search_spec.
    (* Our second alternative for the search spec fits best *)
    start_function.
    forward.
    forward_while
      (EX i:Z,
            PROP  (0 <= i <= length;
                   forall (j : Z), 0 <= j < i -> Znth_opt j contents <> Some target )
         LOCAL ( temp _i (Vint (Int.repr i ) );
                 temp _length (Vint ( Int.repr length ) );
                 temp _target (Vint (Int.repr target));
                 temp _arr arr )
         SEP   ( data_at sh (tarray tint length)
                           (map Vint (map Int.repr contents))
                           arr ) ).
    * (* Loop invariant holds initially; take i = 0 *)
      Exists 0.
      entailer!.
      (* Condition 0 <= j < j is unsatisfiable *)
      move => ? ?; exfalso; omega.
    * (* Some type checking *)
      entailer!.
    * (* Loop invariant is indeed an invariant *)
      assert_PROP (Zlength contents = length). {
        entailer!. do 2 rewrite Zlength_map. reflexivity.
      }
      forward.
      (* Compare current array entry to target *)
      forward_if (
        PROP  ( 0 <= i < length;
                Znth_opt i contents <> Some target )
        LOCAL ( temp _i (Vint (Int.repr i ) );
                temp _length (Vint ( Int.repr length ) );
                temp _target (Vint (Int.repr target));
                temp _arr arr )
        SEP   ( data_at sh (tarray tint length)
                          (map Vint (map Int.repr contents))
                          arr ) ).
      - (* Have found target *)
        forward.
        (* The C-check works on machine integers as opposed to
           abstract integers; we need to use the assumptions on the
           range of the values of the contents list to argue that
           no wraparound has happened and that hence we also also
           have a match of abstract integers. *)
        (* QUESTION: How can I control the names of hypotheses? *)
        move /repr_inj_signed in H5.
        move : H2 => [] H21 H22.
        have H_rep_cont_i : repable_signed (Znth i contents 0).
          apply Forall_Znth; [ by split | by assumption ].
        have H_rep_target : repable_signed target by assumption.
        move /(_ H_rep_cont_i H_rep_target) in H5.
        (* Now we know that there's also a match of abstract integers
           and can use this together with the loop-assumption to show
           that our return value matches the value of the abstract
           search function. *)
        have -> : (search target contents = Some i).
        {
          apply search_spec.
          by rewrite /Znth_opt (Znth_map 0); repeat split; try f_equal.
        }
        entailer.
      - (* Haven't found target *)
        forward.
        entailer.
        (* Again, the comparison is for machine integers, but if there's
           not even a match for machine integers, there can't be one for
           abstract integers either. *)
        have H5' : Znth i contents 0 <> target.
        {
          move => H_eq.
          rewrite H_eq in H5.
          contradiction.
        }
        have H5'' : Znth_opt i contents <> Some target
          by rewrite /Znth_opt (Znth_map 0); [ case; assumption | omega ].
        entailer.
      forward.
      Exists (i+1).
      entailer!.
      (* Need to prove loop invariant for i+1, so essentially we have to split
         the assumption 0 <= j < i+1 into the cases 0 <= j < i and j = i, using
         the loop assumption and the outcome of the branch, respectively. *)
      move => j H_j_le.
      have : j < i \/ j = i.
      {
        (* Only need to discharge j > i *)
        move : (Ztrichotomy j i) => [ | []];
           [ tauto | tauto | move => H_j_gt_i; exfalso; omega ].
      }
      move => [ H_j_lt_i | -> ].
      + (* j < i *)
        by apply H3; omega.
      + (* j = i *)
        assumption.
    * (* We've left the loop - check function postcondition *)
      assert_PROP (Zlength contents = length). {
        entailer!. do 2 rewrite Zlength_map. reflexivity.
      }
      have H_i_len : i = length by omega.
      rewrite H_i_len.
      rewrite H_i_len in H3.
      forward.
      have -> : search target contents = None
        by apply search_none.
      entailer.
  Qed.

End C_search_verify.
