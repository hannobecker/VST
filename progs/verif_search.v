
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
   * Return
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

  Lemma search_ind :
    search_spec0 -> forall (target : X) (lst : list X) (i : Z),
      0 <= i < Zlength lst ->
      search target (sublist 0 i lst) = None ->
      Znth_opt i lst <> Some target ->
      search target (sublist 0 (i + 1) lst) = None.
  Proof.
    move => H_spec target lst i H_i H_search H_nth.
    destruct (search _ (sublist 0 (i+1) lst)) as [ j | ] eqn:H_eq; first exfalso; last done.
    (* Assume on the contrary that search result is positive *)
    move : H_eq.
    move /H_spec => [] H_j [] H_jth H_minimal.
    rewrite Zlength_sublist in H_j; [ | omega | omega ].
    have : (j < i \/ j = i).
      (* Need to exclude j > i *)
      move : (Ztrichotomy j i) => [ | [] ]; [ tauto | tauto | move => H_j_gt_i ].
      omega.
    move => [ H_j_lt_i | H_i_j ].
    * (* j < i *)
      (* If we can find some j < i such that the search is successful,
         we can also find a smallest one. *)
      suffices H_contr: (search target (sublist 0 i lst) = Some j).
        move : H_search.
        rewrite H_contr.
        discriminate.
        apply H_spec; repeat split; try omega.
        * rewrite Zlength_sublist; omega.
        * rewrite /Znth_opt -sublist_map Znth_sublist; try omega.
          rewrite /Znth_opt -sublist_map Znth_sublist in H_jth; try omega.
          assumption.
        * move => j0 H_j0.
          move/(_ j0 H_j0) in H_minimal.
          rewrite /Znth_opt -sublist_map Znth_sublist; try omega.
          rewrite /Znth_opt -sublist_map Znth_sublist in H_minimal; try omega.
          assumption.
    * (* j = i *)
      rewrite H_i_j /Znth_opt -sublist_map Znth_sublist in H_jth; [ | omega | omega ].
      replace (i + 0) with i in H_jth by omega.
      contradiction.
  Qed.

  Lemma search_nil :
    search_spec0 -> forall (target : X), search target [] = None.
  Proof.
    rewrite/search_spec0 => H_spec target.
    move/(_ target []) in H_spec.
    destruct (search target []) as [ i | ] eqn:H_search; last reflexivity.
    (* Assume search has found something *)
    move/(_ i) in H_spec.
    exfalso.
    have : @Znth_opt X i [] = Some target by tauto.
    rewrite/Znth_opt //= Znth_nil. discriminate.
  Qed.

  (* That must be somewhere in the std library... *)
  Definition is_some { X : Type } : option X -> bool :=
    option_rect (fun _ => bool) (fun _ => true) false.

  Definition search_spec1 : Prop :=
    forall (target : X) (lst : list X) (i : Z),
    search target lst = Some i <-> (
      0 <= i < Zlength lst          /\
      Znth_opt i lst = Some target /\
      ~ In target (sublist 0 i lst)).

  Lemma In_Znth { A : Type} (lst : list A) (x d : A) :
    In x lst -> ( exists (i : Z), 0 <= i < Zlength lst /\ Znth i lst d = x ).
  Proof.
    move /(In_nth _ _ d) => [] iN [] ? ?.
    exists (Z.of_nat iN).
    split; first split.
     * by apply Nat2Z.is_nonneg.
    * rewrite Zlength_correct; omega.
    * rewrite /Znth.
      have H_i0 : (Z.of_nat iN) >= 0 by omega.
      rewrite zlt_false; last by assumption.
      by rewrite Nat2Z.id.
  Qed.

  Proposition search_spec_equiv01 :
    search_spec0 <-> search_spec1.
  Proof.
    have H_lem : forall (i : Z) (lst : list X) (target : X), 0 <= i < Zlength lst ->
      ~ In target (sublist 0 i lst)
      <-> ( forall (j : Z), 0 <= j < i -> Znth_opt j lst <> Some target ).
    {
      move => i lst target H_i.
      split; [ move => H_in | move => H_nth ].
      + move => j H_j_lt_i H_nth.
        apply H_in.
        have H_nth' : (Znth j lst target) = target
          by move : H_nth; rewrite /Znth_opt (Znth_map target);
             [ case | omega ].
        have <- : (Znth j (sublist 0 i lst) target) = target
          by rewrite -{2}H_nth' Znth_sublist; first f_equal; omega.
        apply Znth_In; split; last rewrite Zlength_sublist; omega.
      + move /(In_Znth _ _ target) => [].
        move => j [] H_j H_jth.
        move /(_ j) in H_nth.
        rewrite Zlength_sublist in H_j; [ | omega | omega ].
        apply H_nth; first omega.
        rewrite Znth_sublist in H_jth; [ | omega | omega ].
        replace (j + 0) with j in H_jth by omega.
        rewrite /Znth_opt (Znth_map target); [ by f_equal | omega ].
    }
    (* After this lemma, it's just a matter of writing out
     * and splitting all definitions, in both directions *)
    split;
      move => H_asm target lst i;
      move /(_ i lst target) in H_lem;
      move /(_ target lst i) in H_asm;
      tauto.
  Qed.

  Definition search_spec2 : Prop :=
    forall (target : X) (lst : list X) (i : Z),
    search target lst = Some i <-> (
      0 <= i < Zlength lst          /\
      Znth_opt i lst = Some target /\
      search target (sublist 0 i lst) = None ).

  Proposition search_spec_equiv12 :
    search_spec1 <-> search_spec2.
  Admitted.

  Proposition search_spec_equiv02 :
    search_spec0 <-> search_spec2.
  Proof.
    (* Make prover more aware of the previous equivalences
       by putting them in the proof context. *)
    pose search_spec_equiv01.
    pose search_spec_equiv12.
    tauto.
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


Module SearchSpecImpliesDecidableEquality (XTy : Ty) (SImp : SearchImplementation XTy).

  Import SImp.

  Definition eqX (x y : X) : bool :=
    match search x [y] with
    | Some _ => true
    | None   => false
    end.

  Lemma search_refl: forall (x : X), search x [x] = Some 0.
  Proof.
    move => x.
    apply search_spec; split; [ | split ].
    + by rewrite Zlength_cons //=.
    + by rewrite /Znth_opt /Znth //=.
    + move => j [] ? ?; exfalso; omega.
  Qed.

  Lemma eqX_spec : forall (x y : X), eqX x y = true <-> x = y.
  Proof.
    split.
    + (* Assume x, y are equal wrt. eqX / search *)
      rewrite/eqX.
      set search_res := search x [y].
      (* Search must have been successful *)
      destruct search_res as [ i | ] eqn:H_search; [ move => _ | discriminate ].
      (* Apply spec *)
      move /search_spec in H_search.
      move : H_search => [] H_len [] H_nth H_no_earlier.
      (* Only possible search index is i=0 because [y] has length 1 *)
      have H_i0 : i = 0.
      -  move: H_len => [] H_0_le_i H_i_lt_len.
         rewrite Zlength_cons //= in H_i_lt_len.
           omega.
      rewrite H_i0 /Znth_opt /Znth //= in H_nth.
        by inversion H_nth.
    + (* Assume x and y are Leibniz equal *)
      move => ->.
      by rewrite /eqX search_refl.
  Qed.

End SearchSpecImpliesDecidableEquality.


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

  Locate "PROP".
  Print mpred. Print sublist. Locate "=". Search eqb.

  Lemma body_search_alt: semax_body Vprog Gprog f_search_alt Csearch_spec.
  Proof.
    pose search_spec.
    (* Our second alternative for the search spec fits best *)
    have search_spec2 : search_spec2 X search
      by apply search_spec_equiv02; assumption.
    start_function.
    forward.
    forward_while
      (EX i:Z,
         PROP  (0 <= i <= length;
                search target (sublist 0 i contents) = None)
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
      (* Initially, sublist is empty, and hence search result is None;
         That was proved from the spec as `search_nil` above. *)
      by rewrite sublist_nil (search_nil X search search_spec).
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
        (* Now we know that there's also a match of abstrac integers
           and can use this together with the loop-assumption to show
           that our return value matches the value of the abstract
           search function. *)
        have -> : (search target contents = Some i).
        {
          apply search_spec2.
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
      by apply search_ind.
    * (* We've left the loop - check function postcondition *)
      assert_PROP (Zlength contents = length). {
        entailer!. do 2 rewrite Zlength_map. reflexivity.
      }
      move : H3.
      have -> : i = length by omega.
      rewrite sublist_same; [ | done | done ] => H_search_res.
      forward.
      rewrite H_search_res.
      entailer.
Qed.


(* The canonical implementation of a search function for integers *)
Module LinearSearch : SearchImplementation ZTy.

  Import ZTy.

  Fixpoint search (target: X) (lst: list X) { struct lst } : option Z :=
    match lst with
    | nil => None
    | cons a lst' =>
      if Z.eqb a target then
        Some 0%Z
      else
        option_map (Z.add 1) (search target lst')
    end.

  (** Helper lemmas *)

  Lemma sublist_empty { X : Type } (a b : Z) :
    @sublist X a b [] = [].
  Proof.
    by rewrite /sublist skipn_nil firstn_nil.
  Qed.

  Lemma Znth_opt_some { X : Type } (n : Z) (d : X) (lst : list X) :
    0 <= n < Zlength lst -> Znth_opt n lst = Some (Znth n lst d).
  Proof.
    move => H_len.
    by rewrite /Znth_opt (Znth_map d).
  Qed.

  Lemma sublist_0_pos { X : Type } (i : Z) (x : X) (lst : list X) :
    0 < i <= Zlength( x :: lst )
    -> sublist 0 i (x :: lst) = x :: ( sublist 0 (i - 1) lst ).
  Proof.
    move => [].
    move => H_1_le_i H_i_len.
    replace (x :: lst) with ([x] ++ lst) by trivial.
    rewrite Zlength_cons in H_i_len.
    rewrite sublist0_app2; [ done | rewrite Zlength_cons //=; omega ].
  Qed.

  Lemma option_map_inj { X Y : Type } (f : X -> Y) (x : option X) :
    option_map f x = None -> x = None.
  Proof. by case: x. Qed.

  Lemma search_none_cons0 (lst : list Z) (target : Z) (x : Z) :
    search target (x :: lst) = None ->  Z.eqb x target = false.
  Proof.
    move => H.
    apply not_true_is_false => R.
      by rewrite /search R in H.
  Qed.

  Lemma search_none_cons1 (lst : list Z) (target : Z) (x : Z) :
    search target (x :: lst) = None ->
    search target lst = None.
  Proof.
    move => H. move : (H). move: H => /search_none_cons0.
    rewrite {1}/search => ->.
      by move /option_map_inj.
  Qed.

  Lemma Znth_opt_cons { X : Type } (lst : list X) (x : X) (i : Z):
    0 < i -> Znth_opt i (x :: lst) = Znth_opt (i - 1) lst.
  Admitted.

  Lemma search_result (lst : list Z) (target : Z) (i : Z) :
    0 <= i < Zlength lst
    -> search target (sublist 0 i lst) = None  (* No match up to ith entry *)
    -> Znth_opt i lst = Some target            (* i-th entry matches       *)
    -> search target lst = Some i.             (* Then search result is i  *)
  Proof.
    (* Induction lst, the empty case being contradictory *)
    elim: lst i => [ | a lst IH] i; first by move => [] ? /Zlt_not_le.
    move /(_ (i-1)) in IH.
    (* Distinguish i=0 and i<>0 *)
    move => [] H0 H1.
    move: (Zle_lt_or_eq 0 i H0) => [ H_0lti | <- ].
    * (* 0 < i *)
      rewrite sublist_0_pos.
      move => H_search.
      Focus 2.
      split.
    + by assumption.
    + by omega.
      rewrite Znth_opt_cons;
        last by assumption.
      move => H_Znth.
      rewrite /search (search_none_cons0 (sublist 0 (i-1) lst) _ a) -/search;
        last by assumption.
      rewrite -/search IH //=.
    + apply f_equal; omega.
    + rewrite Zlength_cons in H1; omega.
    + by apply (search_none_cons1 _ _ a).
      * (* 0 = i *)
        rewrite /Znth_opt /Znth //=.
        move => _. case => ->;
                    by rewrite Z.eqb_refl.
  Qed.

  Lemma search_spec :
    forall (target : X) (lst : list X) (i : Z),
    search target lst = Some i <-> (
      0 <= i < Zlength lst          /\
      Znth_opt i lst = Some target /\
      forall (j : Z), 0 <= j < i -> Znth_opt j lst <> Some target ).
  Proof.
  Admitted.

  Eval compute in search 5 [ 1; 4; 2; 63; 5; 12 ].
  Eval compute in search 7 [ 1; 4; 2; 63; 5; 12 ].

End LinearSearch.


  (* Definition search_spec : ident * funspec := *)
  (*   DECLARE _search *)
  (*     WITH arr: val, sh: share, contents: list Z, length: Z, target: Z *)
  (*     PRE [ _arr OF (tptr tint), _length OF tint, _target OF tint ] *)
  (*       PROP (readable_share sh; *)
  (*             (* Make sure abstract integers are within *) *)
  (* (*                the representable range of machine integers *) *)
  (*             0 <= length <= Int.max_signed; *)
  (*             Forall (fun x => Int.min_signed <= x <= Int.max_signed ) contents) *)
  (*       LOCAL ( temp _arr    arr; *)
  (*               temp _length (Vint (Int.repr length)); *)
  (*               temp _target (Vint (Int.repr target)) ) *)
  (*       SEP   ( (* length represents the contents of the *) *)
  (* (*                  length `length` array starting at `array`. *) *)
  (*               data_at sh (tarray tint length) *)
  (*                          (map Vint (map Int.repr contents)) *)
  (*                          arr ) *)
  (*     POST [ tint ] *)
  (*       PROP  (True) *)
  (*       LOCAL ( temp ret_temp ( *)
  (*                      (* Convert list index to pointer *) *)
  (*                      match (search target contents) with *)
  (*                      | None (* Nothing found, expect NULL pointe *) *)
  (*                          => nullval *)
  (*                      | Some idx%Z (* Add index to array base *) *)
  (*                          => field_address0 (tarray tint length) *)
  (*                                           [ArraySubsc idx] *)
  (*                                           arr *)
  (*                      end ) ) *)
  (*       SEP   ( (* Data hasn't been modified or freed *) *)
  (*               data_at sh (tarray tint length) *)
  (*                          (map Vint (map Int.repr contents)) *)
  (*                          arr ). *)
