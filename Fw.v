Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Require Import core unscoped hopl translation.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.

Notation lup := nth_error.



(** * Instantiation into System F_w *)

(* Specification of System F_w *)

Inductive has_typeFw (Delta : list kind) (Gamma : list type) : prog -> type -> Prop :=
| ht_var x t : lup Gamma x = Some t
              -> has_typeFw Delta Gamma (var_prog x) t
| ht_tyabs e t k : has_typeFw (k :: Delta) (map (ren_type ↑) Gamma) e t
                  -> has_typeFw Delta Gamma (tyabs k e) (pi k t)
| ht_tmabs e t1 t2 : has_typeFw Delta (t1 :: Gamma) e t2
                    -> has_typeFw Delta Gamma (tmabs t1 e) (arrow t1 t2)
| ht_tyapp e t1 t2 k : has_typeFw Delta Gamma e (pi k t1)
                      -> has_kind Delta t2 k
                      -> has_typeFw Delta Gamma (tyapp e t2) t1[t2..]
| ht_tmapp e1 e2 t1 t2 : has_typeFw Delta Gamma e1 (arrow t1 t2)
                        -> has_typeFw Delta Gamma e2 t1
                        -> has_typeFw Delta Gamma (tmapp e1 e2) t2
| ht_conv e t1 t2 : conv_type t1 t2
                    -> has_typeFw Delta Gamma e t1
                    -> has_typeFw Delta Gamma e t2.

Inductive has_indexFw (Delta : list kind) (Gamma : list type) (Sigma : list index) : exp -> index -> Prop :=
| hi_var q o : lup Sigma q = Some o
              -> has_indexFw Delta Gamma Sigma (var_exp q) o
| hi_cexp phi t o : is_specFw Delta (t :: Gamma) (o :: Sigma) phi
                  -> has_indexFw Delta Gamma Sigma (cexp t o phi) (ref t o)
| hi_exabs q k o : has_indexFw (k :: Delta) (map (ren_type ↑) Gamma) (map (ren_index ↑) Sigma) q o
                  -> has_indexFw Delta Gamma Sigma (exabs k q) (univ k o)
| hi_exapp q k t o : has_indexFw Delta Gamma Sigma q (univ k o)
                    -> has_kind Delta t k
                    -> has_indexFw Delta Gamma Sigma (exapp q t) o[t..]
| hi_conv e o1 o2 : conv_index o1 o2
                    -> has_indexFw Delta Gamma Sigma e o1
                    -> has_indexFw Delta Gamma Sigma e o2

with is_specFw (Delta : list kind) (Gamma : list type) (Sigma : list index) : spec -> Prop :=
| is_implies phi psi : is_specFw Delta Gamma Sigma phi
                  -> is_specFw Delta Gamma Sigma psi
                  -> is_specFw Delta Gamma Sigma (spimplies phi psi)
| is_tyall phi k : is_specFw (k :: Delta) (map (ren_type ↑) Gamma) (map (ren_index ↑) Sigma) phi
                -> is_specFw Delta Gamma Sigma (tyall k phi)
| is_tmall phi t : is_specFw Delta (t :: Gamma) Sigma phi
                  -> is_specFw Delta Gamma Sigma (tmall t phi)
| is_spall phi o : is_specFw Delta Gamma (o :: Sigma) phi
                -> is_index Delta o
                -> is_specFw Delta Gamma Sigma (spall o phi)
| is_holds e t q q' o : has_typeFw Delta Gamma e t
                        -> has_indexFw Delta Gamma Sigma q (ref t o)
                        -> has_indexFw Delta Gamma Sigma q' o
                        -> is_specFw Delta Gamma Sigma (spholds q q' e).

Inductive Fw_prv (A : list spec) : spec -> Prop :=
| Fw_CTX phi : In phi A
               -> Fw_prv A phi
| Fw_II phi psi : Fw_prv (phi :: A) psi
                -> Fw_prv A (spimplies phi psi)
| Fw_IE phi psi : Fw_prv A (spimplies phi psi)
                -> Fw_prv A phi
                -> Fw_prv A psi
| Fw_TAI phi k : Fw_prv (map (ren_spec ↑ id id) A) phi
                 -> Fw_prv A (tyall k phi)
| Fw_TAE phi k t : Fw_prv A (tyall k phi)
                   -> Fw_prv A (subst_spec (t..) var_prog var_exp phi)
| Fw_EAI phi t : Fw_prv (map (ren_spec id ↑ id) A) phi
                 -> Fw_prv A (tmall t phi)
| Fw_EAE phi e t : Fw_prv A (tmall t phi)
                   -> Fw_prv A (subst_spec var_type (e..) var_exp phi)
| Fw_SAI phi o : Fw_prv (map (ren_spec id id ↑) A) phi
                 -> Fw_prv A (spall o phi)
| Fw_SAE phi o q : Fw_prv A (spall o phi)
                   -> Fw_prv A (subst_spec var_type var_prog (q..) phi)
| Fw_CI phi t o e q : Fw_prv A (subst_spec var_type (e..) (q..) phi)
                      -> Fw_prv A (spholds (cexp t o phi) q e)
| Fw_CE phi t o e q : Fw_prv A (spholds (cexp t o phi) q e)
                      -> Fw_prv A (subst_spec var_type (e..) (q..) phi)
| Fw_RED phi e1 e2 : red_prog e1 e2
                    -> Fw_prv A (subst_spec var_type (e2..) var_exp phi)
                    -> Fw_prv A (subst_spec var_type (e1..) var_exp phi)
| Fw_CONV phi psi : conv_spec phi psi
                  -> Fw_prv A phi
                  -> Fw_prv A psi.

Section Fw.

  (* Syntax components *)

  Variable icomp : type -> type.
  Variable iret : prog -> prog.
  Variable ibind : prog -> prog -> prog.
  Variable iafter : prog -> spec -> spec.

  (* Assumptions about reduction and conversion *)

  Hypothesis iret_is_value :
    forall e, is_value (iret e).

  Hypothesis iret_red_prog :
    forall e e', red_prog (ibind (iret e) e') (subst_prog var_type (e..) e').

  Hypothesis ibind_red_prog :
    forall e1 e2 e, red_prog e1 e2 -> red_prog (ibind e1 e) (ibind e2 e).

  Hypothesis icomp_conv :
    forall t t', conv_type t t' -> conv_type (icomp t) (icomp t').

  (* Assumptions about substitution *)

  Hypothesis icomp_subst :
    forall sigma t, (icomp t) [sigma] = icomp (t [sigma]).

  (* Assumptions about typing judgements *)

  Hypothesis icomp_has_kind :
    forall Delta t, has_kind Delta t 0 -> has_kind Delta (icomp t) 0.

  Hypothesis iret_has_type :
    forall Delta Gamma e t, has_typeFw Delta Gamma e t -> has_typeFw Delta Gamma (iret e) (icomp t).
  
  Hypothesis ibind_has_type :
    forall Delta Gamma e e' t t', has_typeFw Delta Gamma e (icomp t)
      -> has_typeFw Delta (t :: Gamma) e' (icomp t')
      -> has_typeFw Delta Gamma (ibind e e') (icomp t').

  Hypothesis iafter_is_spec :
    forall Delta Gamma Sigma e t phi, is_specFw Delta (t :: Gamma) Sigma phi
      -> has_typeFw Delta Gamma e (icomp t)
      -> is_specFw Delta Gamma Sigma (iafter e phi).

  (* Assumptions about deductions *)

  Hypothesis iafter_ret :
    forall A phi e, Fw_prv A (subst_spec var_type (e..) var_exp phi)
      -> Fw_prv A (iafter (iret e) phi).

  Hypothesis iafter_bind :
    forall A phi e1 e2, Fw_prv A (iafter e1 (iafter e2 (ren_spec id swap id phi)))
      -> Fw_prv A (iafter (ibind e1 e2) phi).

  Hypothesis iafter_mono :
    forall A phi psi e, Fw_prv (phi :: map (ren_spec id ↑ id) A) psi
      -> Fw_prv A (iafter e phi)
      -> Fw_prv A (iafter e psi).

  (* Translation of types and preservation lemma *)

  Fixpoint transFw_type (t : type) : type :=
    match t with
    | var_type X => var_type X
    | app t t' => app (transFw_type t) (transFw_type t')
    | abs k t => abs k (transFw_type t)
    | arrow t t' => arrow (transFw_type t) (transFw_type t')
    | pi k t => pi k (transFw_type t)
    | comp t => icomp (transFw_type t)
    end.

  Lemma transFw_type_has_kind Delta t k :
    has_kind Delta t k -> has_kind Delta (transFw_type t) k.
  Proof.
    induction 1; cbn; try econstructor; eauto.
  Qed.

  (* Translation of programs and preservation lemma *)
    
  Fixpoint transFw_prog (e : prog) : prog :=
    match e with
    | var_prog x => var_prog x
    | tyabs k e => tyabs k (transFw_prog e)
    | tmabs t e => tmabs (transFw_type t) (transFw_prog e)
    | tyapp e t => tyapp (transFw_prog e) (transFw_type t)
    | tmapp e e' => tmapp (transFw_prog e) (transFw_prog e')
    | ret e => iret (transFw_prog e)
    | bind e e' => ibind (transFw_prog e) (transFw_prog e')
    end.

  Lemma transFw_type_ren xi t :
    (transFw_type t) ⟨xi⟩ = transFw_type t ⟨xi⟩.
  Proof.
    induction t in xi |- *; cbn in *.
    - reflexivity.
    - now rewrite IHt1, IHt2.
    - now rewrite <- IHt.
    - now rewrite IHt1, IHt2.
    - now rewrite <- IHt.
    - now rewrite <- IHt, !rinstInst'_type, icomp_subst.
  Qed.

  Lemma transFw_type_ren_ctx xi Gamma :
    list_map (ren_type xi) (list_map transFw_type Gamma)
      = list_map transFw_type (list_map (ren_type xi) Gamma).
  Proof.
    rewrite !map_map. apply map_ext. apply transFw_type_ren.
  Qed.

  Lemma transFw_type_subst sigma t :
    (transFw_type t) [sigma >> transFw_type] = transFw_type t [sigma].
  Proof.
    induction t in sigma |- *; cbn in *.
    - reflexivity.
    - now rewrite IHt1, IHt2.
    - rewrite <- IHt. f_equal. apply ext_type. intros []; cbn; trivial.
      unfold funcomp. apply transFw_type_ren.
    - now rewrite IHt1, IHt2.
    - rewrite <- IHt. f_equal. apply ext_type. intros []; cbn; trivial.
      unfold funcomp. apply transFw_type_ren.
    - now rewrite <- IHt, icomp_subst.
  Qed.

  Lemma transFw_type_conv t t' :
    conv_type t t' -> conv_type (transFw_type t) (transFw_type t').
  Proof.
    induction 1; cbn in *; try now (econstructor; eauto).
    - constructor 4. rewrite H. rewrite <- transFw_type_subst. apply ext_type. now intros [].
    - now apply icomp_conv.
  Qed.

  Lemma transFw_prog_has_type Delta Gamma e t :
    has_type Delta Gamma e t
      -> has_typeFw Delta (map transFw_type Gamma) (transFw_prog e) (transFw_type t).
  Proof.
    induction 1; cbn in *.
    - constructor 1. now apply map_nth_error.
    - constructor 2. now rewrite transFw_type_ren_ctx.
    - constructor 3. apply IHhas_type.
    - now apply iret_has_type.
    - eapply ibind_has_type; eauto.
    - rewrite <- transFw_type_subst. erewrite ext_type.
      + econstructor 4; eauto. now apply transFw_type_has_kind.
      + now intros [].
    - econstructor 5; eauto.
    - econstructor 6; eauto. now apply transFw_type_conv.
  Qed.

  (* Translation of indices and preservation lemma *)

  Fixpoint transFw_index (o : index) : index :=
    match o with
    | refb t => refb (transFw_type t)
    | ref t o => ref (transFw_type t) (transFw_index o)
    | univ k o => univ k (transFw_index o)
    end.

  Lemma transFw_index_is_index Delta o :
    is_index Delta o -> is_index Delta (transFw_index o).
  Proof.
    induction 1; cbn in *.
    - constructor. now apply transFw_type_has_kind.
    - constructor; trivial. now apply transFw_type_has_kind.
    - constructor. assumption.
  Qed.

  (* Translation of specifications and expressions and preservation lemmas *)

  Fixpoint transFw_spec (phi : spec) : spec :=
    match phi with
    | spholds q q' e => spholds (transFw_exp q) (transFw_exp q') (transFw_prog e)
    | spimplies phi psi => spimplies (transFw_spec phi) (transFw_spec psi)
    | after e phi => iafter (transFw_prog e) (transFw_spec phi)
    | tyall k phi => tyall k (transFw_spec phi)
    | tmall t phi => tmall (transFw_type t) (transFw_spec phi)
    | spall o phi => spall (transFw_index o) (transFw_spec phi)
    end
  with transFw_exp (q : exp) : exp :=
    match q with
    | var_exp x => var_exp x
    | cexp t o phi => cexp (transFw_type t) (transFw_index o) (transFw_spec phi)
    | exabs k q => exabs k (transFw_exp q)
    | exapp q t => exapp (transFw_exp q) (transFw_type t)
  end.

  Lemma transFw_index_subst sigma o :
    (transFw_index o) [sigma >> transFw_type] = transFw_index o [sigma].
  Proof.
    induction o in sigma |- *; cbn in *.
    - now rewrite transFw_type_subst.
    - now rewrite transFw_type_subst, IHo.
    - rewrite <- IHo. f_equal. apply ext_index. intros []; cbn; trivial.
      unfold funcomp. apply transFw_type_ren.
  Qed.

  Lemma transFw_index_ren xi o :
    (transFw_index o) ⟨xi⟩ = transFw_index o ⟨xi⟩.
  Proof.
    rewrite !rinstInst'_index. rewrite <- transFw_index_subst. now apply ext_index.
  Qed.

  Lemma transFw_index_conv o o' :
    conv_index o o' -> conv_index (transFw_index o) (transFw_index o').
  Proof.
    induction 1; cbn in *; try now (econstructor; eauto).
    - constructor 4. now apply transFw_type_conv.
    - constructor 5. now apply transFw_type_conv.
  Qed.

  Lemma transFw_index_ren_ctx xi Sigma :
    list_map (ren_index xi) (list_map transFw_index Sigma)
      = list_map transFw_index (list_map (ren_index xi) Sigma).
  Proof.
    rewrite !map_map. apply map_ext. apply transFw_index_ren.
  Qed.

  Lemma transFw_spec_is_spec Delta Gamma Sigma phi :
    is_spec Delta Gamma Sigma phi
      -> is_specFw Delta (map transFw_type Gamma) (map transFw_index Sigma) (transFw_spec phi)
  with transFw_exp_has_index Delta Gamma Sigma q o :
    has_index Delta Gamma Sigma q o
      -> has_indexFw Delta (map transFw_type Gamma) (map transFw_index Sigma) (transFw_exp q) (transFw_index o).
  Proof.
    induction 1; cbn in *.
    - constructor 1; eauto.
    - eapply iafter_is_spec; eauto. now apply transFw_prog_has_type in H0.
    - constructor 2. now rewrite transFw_type_ren_ctx, transFw_index_ren_ctx.
    - constructor 3. assumption.
    - constructor 4; trivial. now apply transFw_index_is_index.
    - apply transFw_prog_has_type in H.
      apply transFw_exp_has_index in H0, H1.
      econstructor 5; eauto.
    - induction 1; cbn in *.
      + constructor 1. now apply map_nth_error.
      + constructor 2. now apply transFw_spec_is_spec in H.
      + constructor 3. now rewrite transFw_type_ren_ctx, transFw_index_ren_ctx.
      + rewrite <- transFw_index_subst. erewrite ext_index.
        * econstructor 4; eauto. now apply transFw_type_has_kind.
        * now intros [].
      + econstructor 5; eauto. now apply transFw_index_conv.
  Qed.

  (* Soundness of translation of HOPL into F_w *)

  Lemma transFw_prog_subst xi1 xi2 e :
    subst_prog (xi1 >> transFw_type) (xi2 >> transFw_prog) (transFw_prog e)
      = transFw_prog (subst_prog xi1 xi2 e).
  Proof.
  Admitted.

  Lemma transFw_spec_ren xi1 xi2 xi3 phi :
    ren_spec xi1 xi2 xi3 (transFw_spec phi)
      = transFw_spec (ren_spec xi1 xi2 xi3 phi).
  Proof.
  Admitted.

  Lemma transFw_spec_ren_ctx xi1 xi2 xi3 Phi :
    list_map (ren_spec xi1 xi2 xi3) (list_map transFw_spec Phi)
      = list_map transFw_spec (list_map (ren_spec xi1 xi2 xi3) Phi).
  Proof.
    rewrite !map_map. apply map_ext. apply transFw_spec_ren.
  Qed.

  Lemma transFw_spec_subst xi1 xi2 xi3 phi :
    subst_spec (xi1 >> transFw_type) (xi2 >> transFw_prog) (xi3 >> transFw_exp) (transFw_spec phi)
      = transFw_spec (subst_spec xi1 xi2 xi3 phi).
  Proof.
  Admitted.

  Lemma transFw_prog_is_value e :
    is_value e -> is_value (transFw_prog e).
  Proof.
    induction 1; cbn in *; try constructor.
    apply iret_is_value.
  Qed.

  Lemma transFw_prog_red e e' :
    red_prog e e' -> red_prog (transFw_prog e) (transFw_prog e').
  Proof.
    induction 1; cbn in *.
    - econstructor 1; eauto.
    - subst. constructor 2. rewrite <- transFw_prog_subst. apply ext_prog. all: now intros [].
    - subst. constructor 3; try now apply transFw_prog_is_value.
      rewrite <- transFw_prog_subst. apply ext_prog. all: now intros [].
    - subst. rewrite <- transFw_prog_subst. erewrite ext_prog. apply iret_red_prog. all: now intros [].
    - now constructor.
    - now constructor.
    - constructor. assumption. now apply transFw_prog_is_value.
    - now apply ibind_red_prog.
  Qed.

  Lemma transFw_spec_conv phi psi :
    conv_spec phi psi -> conv_spec (transFw_spec phi) (transFw_spec psi).
  Proof.
  Admitted.

  Lemma HOPL_Fw Phi phi :
    HOPL_prv Phi phi -> Fw_prv (map transFw_spec Phi) (transFw_spec phi).
  Proof.
    induction 1; cbn in *.
    - constructor 1. now apply in_map.
    - now constructor 2.
    - econstructor 3; eauto.
    - constructor 4. now rewrite transFw_spec_ren_ctx.
    - rewrite <- transFw_spec_subst. erewrite ext_spec.
      econstructor 5. eassumption. all: now intros [].
    - constructor 6. now rewrite transFw_spec_ren_ctx.
    - rewrite <- transFw_spec_subst. erewrite ext_spec.
      econstructor 7. eassumption. all: now intros [].
    - constructor 8. now rewrite transFw_spec_ren_ctx.
    - rewrite <- transFw_spec_subst. erewrite ext_spec.
      econstructor 9. eassumption. all: now intros [].
    - constructor 10. rewrite <- transFw_spec_subst in IHHOPL_prv.
      erewrite ext_spec. eassumption. all: now intros [].
    - rewrite <- transFw_spec_subst. erewrite ext_spec.
      econstructor 11. eassumption. all: now intros [].
    - apply iafter_ret. rewrite <- transFw_spec_subst in IHHOPL_prv.
      erewrite ext_spec. eassumption. all: now intros [].
    - apply iafter_bind. now rewrite transFw_spec_ren.
    - eapply iafter_mono; eauto. now rewrite transFw_spec_ren_ctx.
    - rewrite <- transFw_spec_subst in *. erewrite ext_spec.
      econstructor 12. apply transFw_prog_red. eassumption.
      erewrite ext_spec. eassumption. all: now intros [].
    - econstructor 13; eauto. now apply transFw_spec_conv.
  Qed.

  (* Combined translation of iHOL into F_w *)

  Definition trans_T' psi :=
    transFw_type (trans_T psi).

  Definition trans_S' psi e :=
    transFw_spec (trans_S psi e).

  Definition trans_SL' Psi :=
    map transFw_spec (trans_SL Psi).

  Theorem soundness_Fw Xi Psi psi :
    THOL_prv Xi Psi psi
      -> exists p, has_typeFw Xi (map trans_T' Psi) p (icomp (trans_T' psi))
        /\ Fw_prv (trans_SL' Psi) (iafter p (trans_S' psi (var_prog 0))).
  Proof.
    intros (p & H1 & H2) % soundness.
    exists (transFw_prog p). split.
    - apply transFw_prog_has_type in H1. rewrite map_map in H1. apply H1.
    - apply HOPL_Fw in H2. apply H2.
  Qed.

End Fw.

(* Trivial instantiation *)

Module Trivial.

  Variable t0 : type.

  Definition icomp (t : type) := t.
  Definition iret (e : prog) := e.
  Definition ibind (e e' : prog) := tmapp (tmabs t0 e') e.
  Definition iafter (e : prog) (phi : spec) := phi.

  Lemma instantiate Xi Psi psi :
    THOL_prv Xi Psi psi -> True.
  Proof.
    intros H. apply (@soundness_Fw icomp iret ibind iafter) in H.
    - admit.
    - admit.
    - intros e e'. apply rp_betatm; trivial. admit.
    - intros e1 e2 e He. apply rp_tmapp2; trivial. constructor.
    - tauto.
    - tauto.
    - tauto.
    - tauto.
    - intros. eapply ht_tmapp.
      + apply ht_tmabs. admit.
      + admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

End Trivial.
