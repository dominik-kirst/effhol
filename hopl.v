Require Import core unscoped.

Require Import core_axioms unscoped_axioms.
Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive type : Type :=
  | var_type : nat -> type
  | app : type -> type -> type
  | abs : nat -> type -> type
  | arrow : type -> type -> type
  | pi : nat -> type -> type
  | comp : type -> type.

Lemma congr_app {s0 : type} {s1 : type} {t0 : type} {t1 : type}
  (H0 : s0 = t0) (H1 : s1 = t1) : app s0 s1 = app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => app x s1) H0))
         (ap (fun x => app t0 x) H1)).
Qed.

Lemma congr_abs {s0 : nat} {s1 : type} {t0 : nat} {t1 : type} (H0 : s0 = t0)
  (H1 : s1 = t1) : abs s0 s1 = abs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => abs x s1) H0))
         (ap (fun x => abs t0 x) H1)).
Qed.

Lemma congr_arrow {s0 : type} {s1 : type} {t0 : type} {t1 : type}
  (H0 : s0 = t0) (H1 : s1 = t1) : arrow s0 s1 = arrow t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => arrow x s1) H0))
         (ap (fun x => arrow t0 x) H1)).
Qed.

Lemma congr_pi {s0 : nat} {s1 : type} {t0 : nat} {t1 : type} (H0 : s0 = t0)
  (H1 : s1 = t1) : pi s0 s1 = pi t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => pi x s1) H0))
         (ap (fun x => pi t0 x) H1)).
Qed.

Lemma congr_comp {s0 : type} {t0 : type} (H0 : s0 = t0) : comp s0 = comp t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => comp x) H0)).
Qed.

Lemma upRen_type_type (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_type (xi_type : nat -> nat) (s : type) {struct s} : type :=
  match s with
  | var_type s0 => var_type (xi_type s0)
  | app s0 s1 => app (ren_type xi_type s0) (ren_type xi_type s1)
  | abs s0 s1 => abs s0 (ren_type (upRen_type_type xi_type) s1)
  | arrow s0 s1 => arrow (ren_type xi_type s0) (ren_type xi_type s1)
  | pi s0 s1 => pi s0 (ren_type (upRen_type_type xi_type) s1)
  | comp s0 => comp (ren_type xi_type s0)
  end.

Lemma up_type_type (sigma : nat -> type) : nat -> type.
Proof.
exact (scons (var_type var_zero) (funcomp (ren_type shift) sigma)).
Defined.

Fixpoint subst_type (sigma_type : nat -> type) (s : type) {struct s} : 
type :=
  match s with
  | var_type s0 => sigma_type s0
  | app s0 s1 => app (subst_type sigma_type s0) (subst_type sigma_type s1)
  | abs s0 s1 => abs s0 (subst_type (up_type_type sigma_type) s1)
  | arrow s0 s1 =>
      arrow (subst_type sigma_type s0) (subst_type sigma_type s1)
  | pi s0 s1 => pi s0 (subst_type (up_type_type sigma_type) s1)
  | comp s0 => comp (subst_type sigma_type s0)
  end.

Lemma upId_type_type (sigma : nat -> type)
  (Eq : forall x, sigma x = var_type x) :
  forall x, up_type_type sigma x = var_type x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_type shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_type (sigma_type : nat -> type)
(Eq_type : forall x, sigma_type x = var_type x) (s : type) {struct s} :
subst_type sigma_type s = s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app (idSubst_type sigma_type Eq_type s0)
        (idSubst_type sigma_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (idSubst_type (up_type_type sigma_type) (upId_type_type _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow (idSubst_type sigma_type Eq_type s0)
        (idSubst_type sigma_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (idSubst_type (up_type_type sigma_type) (upId_type_type _ Eq_type) s1)
  | comp s0 => congr_comp (idSubst_type sigma_type Eq_type s0)
  end.

Lemma upExtRen_type_type (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_type_type xi x = upRen_type_type zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_type (xi_type : nat -> nat) (zeta_type : nat -> nat)
(Eq_type : forall x, xi_type x = zeta_type x) (s : type) {struct s} :
ren_type xi_type s = ren_type zeta_type s :=
  match s with
  | var_type s0 => ap (var_type) (Eq_type s0)
  | app s0 s1 =>
      congr_app (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_type xi_type zeta_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (extRen_type (upRen_type_type xi_type) (upRen_type_type zeta_type)
           (upExtRen_type_type _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_type xi_type zeta_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (extRen_type (upRen_type_type xi_type) (upRen_type_type zeta_type)
           (upExtRen_type_type _ _ Eq_type) s1)
  | comp s0 => congr_comp (extRen_type xi_type zeta_type Eq_type s0)
  end.

Lemma upExt_type_type (sigma : nat -> type) (tau : nat -> type)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_type_type sigma x = up_type_type tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_type shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_type (sigma_type : nat -> type) (tau_type : nat -> type)
(Eq_type : forall x, sigma_type x = tau_type x) (s : type) {struct s} :
subst_type sigma_type s = subst_type tau_type s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app (ext_type sigma_type tau_type Eq_type s0)
        (ext_type sigma_type tau_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (ext_type (up_type_type sigma_type) (up_type_type tau_type)
           (upExt_type_type _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow (ext_type sigma_type tau_type Eq_type s0)
        (ext_type sigma_type tau_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (ext_type (up_type_type sigma_type) (up_type_type tau_type)
           (upExt_type_type _ _ Eq_type) s1)
  | comp s0 => congr_comp (ext_type sigma_type tau_type Eq_type s0)
  end.

Lemma up_ren_ren_type_type (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_type_type zeta) (upRen_type_type xi) x =
  upRen_type_type rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_type (xi_type : nat -> nat) (zeta_type : nat -> nat)
(rho_type : nat -> nat)
(Eq_type : forall x, funcomp zeta_type xi_type x = rho_type x) (s : type)
{struct s} : ren_type zeta_type (ren_type xi_type s) = ren_type rho_type s :=
  match s with
  | var_type s0 => ap (var_type) (Eq_type s0)
  | app s0 s1 =>
      congr_app (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_type xi_type zeta_type rho_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (compRenRen_type (upRen_type_type xi_type)
           (upRen_type_type zeta_type) (upRen_type_type rho_type)
           (up_ren_ren _ _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_type xi_type zeta_type rho_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (compRenRen_type (upRen_type_type xi_type)
           (upRen_type_type zeta_type) (upRen_type_type rho_type)
           (up_ren_ren _ _ _ Eq_type) s1)
  | comp s0 =>
      congr_comp (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
  end.

Lemma up_ren_subst_type_type (xi : nat -> nat) (tau : nat -> type)
  (theta : nat -> type) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_type_type tau) (upRen_type_type xi) x = up_type_type theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_type shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_type (xi_type : nat -> nat) (tau_type : nat -> type)
(theta_type : nat -> type)
(Eq_type : forall x, funcomp tau_type xi_type x = theta_type x) (s : type)
{struct s} :
subst_type tau_type (ren_type xi_type s) = subst_type theta_type s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_type xi_type tau_type theta_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (compRenSubst_type (upRen_type_type xi_type) (up_type_type tau_type)
           (up_type_type theta_type) (up_ren_subst_type_type _ _ _ Eq_type)
           s1)
  | arrow s0 s1 =>
      congr_arrow (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_type xi_type tau_type theta_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (compRenSubst_type (upRen_type_type xi_type) (up_type_type tau_type)
           (up_type_type theta_type) (up_ren_subst_type_type _ _ _ Eq_type)
           s1)
  | comp s0 =>
      congr_comp (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
  end.

Lemma up_subst_ren_type_type (sigma : nat -> type) (zeta_type : nat -> nat)
  (theta : nat -> type)
  (Eq : forall x, funcomp (ren_type zeta_type) sigma x = theta x) :
  forall x,
  funcomp (ren_type (upRen_type_type zeta_type)) (up_type_type sigma) x =
  up_type_type theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_type shift (upRen_type_type zeta_type)
                (funcomp shift zeta_type) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_type zeta_type shift (funcomp shift zeta_type)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_type shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_type (sigma_type : nat -> type)
(zeta_type : nat -> nat) (theta_type : nat -> type)
(Eq_type : forall x, funcomp (ren_type zeta_type) sigma_type x = theta_type x)
(s : type) {struct s} :
ren_type zeta_type (subst_type sigma_type s) = subst_type theta_type s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (compSubstRen_type (up_type_type sigma_type)
           (upRen_type_type zeta_type) (up_type_type theta_type)
           (up_subst_ren_type_type _ _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (compSubstRen_type (up_type_type sigma_type)
           (upRen_type_type zeta_type) (up_type_type theta_type)
           (up_subst_ren_type_type _ _ _ Eq_type) s1)
  | comp s0 =>
      congr_comp
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
  end.

Lemma up_subst_subst_type_type (sigma : nat -> type) (tau_type : nat -> type)
  (theta : nat -> type)
  (Eq : forall x, funcomp (subst_type tau_type) sigma x = theta x) :
  forall x,
  funcomp (subst_type (up_type_type tau_type)) (up_type_type sigma) x =
  up_type_type theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_type shift (up_type_type tau_type)
                (funcomp (up_type_type tau_type) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_type tau_type shift
                      (funcomp (ren_type shift) tau_type) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_type shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_type (sigma_type : nat -> type)
(tau_type : nat -> type) (theta_type : nat -> type)
(Eq_type : forall x,
           funcomp (subst_type tau_type) sigma_type x = theta_type x)
(s : type) {struct s} :
subst_type tau_type (subst_type sigma_type s) = subst_type theta_type s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (compSubstSubst_type (up_type_type sigma_type)
           (up_type_type tau_type) (up_type_type theta_type)
           (up_subst_subst_type_type _ _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (compSubstSubst_type (up_type_type sigma_type)
           (up_type_type tau_type) (up_type_type theta_type)
           (up_subst_subst_type_type _ _ _ Eq_type) s1)
  | comp s0 =>
      congr_comp
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
  end.

Lemma renRen_type (xi_type : nat -> nat) (zeta_type : nat -> nat) (s : type)
  :
  ren_type zeta_type (ren_type xi_type s) =
  ren_type (funcomp zeta_type xi_type) s.
Proof.
exact (compRenRen_type xi_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_type_pointwise (xi_type : nat -> nat) (zeta_type : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_type zeta_type) (ren_type xi_type))
    (ren_type (funcomp zeta_type xi_type)).
Proof.
exact (fun s => compRenRen_type xi_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_type (xi_type : nat -> nat) (tau_type : nat -> type)
  (s : type) :
  subst_type tau_type (ren_type xi_type s) =
  subst_type (funcomp tau_type xi_type) s.
Proof.
exact (compRenSubst_type xi_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_type_pointwise (xi_type : nat -> nat) (tau_type : nat -> type)
  :
  pointwise_relation _ eq (funcomp (subst_type tau_type) (ren_type xi_type))
    (subst_type (funcomp tau_type xi_type)).
Proof.
exact (fun s => compRenSubst_type xi_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma substRen_type (sigma_type : nat -> type) (zeta_type : nat -> nat)
  (s : type) :
  ren_type zeta_type (subst_type sigma_type s) =
  subst_type (funcomp (ren_type zeta_type) sigma_type) s.
Proof.
exact (compSubstRen_type sigma_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma substRen_type_pointwise (sigma_type : nat -> type)
  (zeta_type : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_type zeta_type) (subst_type sigma_type))
    (subst_type (funcomp (ren_type zeta_type) sigma_type)).
Proof.
exact (fun s => compSubstRen_type sigma_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_type (sigma_type : nat -> type) (tau_type : nat -> type)
  (s : type) :
  subst_type tau_type (subst_type sigma_type s) =
  subst_type (funcomp (subst_type tau_type) sigma_type) s.
Proof.
exact (compSubstSubst_type sigma_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_type_pointwise (sigma_type : nat -> type)
  (tau_type : nat -> type) :
  pointwise_relation _ eq
    (funcomp (subst_type tau_type) (subst_type sigma_type))
    (subst_type (funcomp (subst_type tau_type) sigma_type)).
Proof.
exact (fun s =>
       compSubstSubst_type sigma_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_type_type (xi : nat -> nat) (sigma : nat -> type)
  (Eq : forall x, funcomp (var_type) xi x = sigma x) :
  forall x, funcomp (var_type) (upRen_type_type xi) x = up_type_type sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_type shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_type (xi_type : nat -> nat) (sigma_type : nat -> type)
(Eq_type : forall x, funcomp (var_type) xi_type x = sigma_type x) (s : type)
{struct s} : ren_type xi_type s = subst_type sigma_type s :=
  match s with
  | var_type s0 => Eq_type s0
  | app s0 s1 =>
      congr_app (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_type xi_type sigma_type Eq_type s1)
  | abs s0 s1 =>
      congr_abs (eq_refl s0)
        (rinst_inst_type (upRen_type_type xi_type) (up_type_type sigma_type)
           (rinstInst_up_type_type _ _ Eq_type) s1)
  | arrow s0 s1 =>
      congr_arrow (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_type xi_type sigma_type Eq_type s1)
  | pi s0 s1 =>
      congr_pi (eq_refl s0)
        (rinst_inst_type (upRen_type_type xi_type) (up_type_type sigma_type)
           (rinstInst_up_type_type _ _ Eq_type) s1)
  | comp s0 => congr_comp (rinst_inst_type xi_type sigma_type Eq_type s0)
  end.

Lemma rinstInst'_type (xi_type : nat -> nat) (s : type) :
  ren_type xi_type s = subst_type (funcomp (var_type) xi_type) s.
Proof.
exact (rinst_inst_type xi_type _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_type_pointwise (xi_type : nat -> nat) :
  pointwise_relation _ eq (ren_type xi_type)
    (subst_type (funcomp (var_type) xi_type)).
Proof.
exact (fun s => rinst_inst_type xi_type _ (fun n => eq_refl) s).
Qed.

Lemma instId'_type (s : type) : subst_type (var_type) s = s.
Proof.
exact (idSubst_type (var_type) (fun n => eq_refl) s).
Qed.

Lemma instId'_type_pointwise :
  pointwise_relation _ eq (subst_type (var_type)) id.
Proof.
exact (fun s => idSubst_type (var_type) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_type (s : type) : ren_type id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_type s) (rinstInst'_type id s)).
Qed.

Lemma rinstId'_type_pointwise : pointwise_relation _ eq (@ren_type id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_type s) (rinstInst'_type id s)).
Qed.

Lemma varL'_type (sigma_type : nat -> type) (x : nat) :
  subst_type sigma_type (var_type x) = sigma_type x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_type_pointwise (sigma_type : nat -> type) :
  pointwise_relation _ eq (funcomp (subst_type sigma_type) (var_type))
    sigma_type.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_type (xi_type : nat -> nat) (x : nat) :
  ren_type xi_type (var_type x) = var_type (xi_type x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_type_pointwise (xi_type : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_type xi_type) (var_type))
    (funcomp (var_type) xi_type).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive prog : Type :=
  | var_prog : nat -> prog
  | tyabs : nat -> prog -> prog
  | tmabs : type -> prog -> prog
  | tyapp : prog -> type -> prog
  | tmapp : prog -> prog -> prog
  | ret : prog -> prog
  | bind : prog -> prog -> prog.

Lemma congr_tyabs {s0 : nat} {s1 : prog} {t0 : nat} {t1 : prog}
  (H0 : s0 = t0) (H1 : s1 = t1) : tyabs s0 s1 = tyabs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tyabs x s1) H0))
         (ap (fun x => tyabs t0 x) H1)).
Qed.

Lemma congr_tmabs {s0 : type} {s1 : prog} {t0 : type} {t1 : prog}
  (H0 : s0 = t0) (H1 : s1 = t1) : tmabs s0 s1 = tmabs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tmabs x s1) H0))
         (ap (fun x => tmabs t0 x) H1)).
Qed.

Lemma congr_tyapp {s0 : prog} {s1 : type} {t0 : prog} {t1 : type}
  (H0 : s0 = t0) (H1 : s1 = t1) : tyapp s0 s1 = tyapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tyapp x s1) H0))
         (ap (fun x => tyapp t0 x) H1)).
Qed.

Lemma congr_tmapp {s0 : prog} {s1 : prog} {t0 : prog} {t1 : prog}
  (H0 : s0 = t0) (H1 : s1 = t1) : tmapp s0 s1 = tmapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tmapp x s1) H0))
         (ap (fun x => tmapp t0 x) H1)).
Qed.

Lemma congr_ret {s0 : prog} {t0 : prog} (H0 : s0 = t0) : ret s0 = ret t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ret x) H0)).
Qed.

Lemma congr_bind {s0 : prog} {s1 : prog} {t0 : prog} {t1 : prog}
  (H0 : s0 = t0) (H1 : s1 = t1) : bind s0 s1 = bind t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => bind x s1) H0))
         (ap (fun x => bind t0 x) H1)).
Qed.

Lemma upRen_type_prog (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_prog_type (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_prog_prog (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_prog (xi_type : nat -> nat) (xi_prog : nat -> nat) (s : prog)
{struct s} : prog :=
  match s with
  | var_prog s0 => var_prog (xi_prog s0)
  | tyabs s0 s1 =>
      tyabs s0
        (ren_prog (upRen_type_type xi_type) (upRen_type_prog xi_prog) s1)
  | tmabs s0 s1 =>
      tmabs (ren_type xi_type s0)
        (ren_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog) s1)
  | tyapp s0 s1 => tyapp (ren_prog xi_type xi_prog s0) (ren_type xi_type s1)
  | tmapp s0 s1 =>
      tmapp (ren_prog xi_type xi_prog s0) (ren_prog xi_type xi_prog s1)
  | ret s0 => ret (ren_prog xi_type xi_prog s0)
  | bind s0 s1 =>
      bind (ren_prog xi_type xi_prog s0)
        (ren_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog) s1)
  end.

Lemma up_type_prog (sigma : nat -> prog) : nat -> prog.
Proof.
exact (funcomp (ren_prog shift id) sigma).
Defined.

Lemma up_prog_type (sigma : nat -> type) : nat -> type.
Proof.
exact (funcomp (ren_type id) sigma).
Defined.

Lemma up_prog_prog (sigma : nat -> prog) : nat -> prog.
Proof.
exact (scons (var_prog var_zero) (funcomp (ren_prog id shift) sigma)).
Defined.

Fixpoint subst_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(s : prog) {struct s} : prog :=
  match s with
  | var_prog s0 => sigma_prog s0
  | tyabs s0 s1 =>
      tyabs s0
        (subst_prog (up_type_type sigma_type) (up_type_prog sigma_prog) s1)
  | tmabs s0 s1 =>
      tmabs (subst_type sigma_type s0)
        (subst_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog) s1)
  | tyapp s0 s1 =>
      tyapp (subst_prog sigma_type sigma_prog s0) (subst_type sigma_type s1)
  | tmapp s0 s1 =>
      tmapp (subst_prog sigma_type sigma_prog s0)
        (subst_prog sigma_type sigma_prog s1)
  | ret s0 => ret (subst_prog sigma_type sigma_prog s0)
  | bind s0 s1 =>
      bind (subst_prog sigma_type sigma_prog s0)
        (subst_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog) s1)
  end.

Lemma upId_type_prog (sigma : nat -> prog)
  (Eq : forall x, sigma x = var_prog x) :
  forall x, up_type_prog sigma x = var_prog x.
Proof.
exact (fun n => ap (ren_prog shift id) (Eq n)).
Qed.

Lemma upId_prog_type (sigma : nat -> type)
  (Eq : forall x, sigma x = var_type x) :
  forall x, up_prog_type sigma x = var_type x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma upId_prog_prog (sigma : nat -> prog)
  (Eq : forall x, sigma x = var_prog x) :
  forall x, up_prog_prog sigma x = var_prog x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_prog id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(Eq_type : forall x, sigma_type x = var_type x)
(Eq_prog : forall x, sigma_prog x = var_prog x) (s : prog) {struct s} :
subst_prog sigma_type sigma_prog s = s :=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (idSubst_prog (up_type_type sigma_type) (up_type_prog sigma_prog)
           (upId_type_type _ Eq_type) (upId_type_prog _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs (idSubst_type sigma_type Eq_type s0)
        (idSubst_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (upId_prog_type _ Eq_type) (upId_prog_prog _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s0)
        (idSubst_type sigma_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s0)
        (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s0)
        (idSubst_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (upId_prog_type _ Eq_type) (upId_prog_prog _ Eq_prog) s1)
  end.

Lemma upExtRen_type_prog (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_type_prog xi x = upRen_type_prog zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_prog_type (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_prog_type xi x = upRen_prog_type zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_prog_prog (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_prog_prog xi x = upRen_prog_prog zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
(zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(Eq_type : forall x, xi_type x = zeta_type x)
(Eq_prog : forall x, xi_prog x = zeta_prog x) (s : prog) {struct s} :
ren_prog xi_type xi_prog s = ren_prog zeta_type zeta_prog s :=
  match s with
  | var_prog s0 => ap (var_prog) (Eq_prog s0)
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (extRen_prog (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_type zeta_type) (upRen_type_prog zeta_prog)
           (upExtRen_type_type _ _ Eq_type) (upExtRen_type_prog _ _ Eq_prog)
           s1)
  | tmabs s0 s1 =>
      congr_tmabs (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upExtRen_prog_type _ _ Eq_type) (upExtRen_prog_prog _ _ Eq_prog)
           s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s0)
        (extRen_type xi_type zeta_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s0)
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s0)
        (extRen_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upExtRen_prog_type _ _ Eq_type) (upExtRen_prog_prog _ _ Eq_prog)
           s1)
  end.

Lemma upExt_type_prog (sigma : nat -> prog) (tau : nat -> prog)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_type_prog sigma x = up_type_prog tau x.
Proof.
exact (fun n => ap (ren_prog shift id) (Eq n)).
Qed.

Lemma upExt_prog_type (sigma : nat -> type) (tau : nat -> type)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_prog_type sigma x = up_prog_type tau x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma upExt_prog_prog (sigma : nat -> prog) (tau : nat -> prog)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_prog_prog sigma x = up_prog_prog tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_prog id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(tau_type : nat -> type) (tau_prog : nat -> prog)
(Eq_type : forall x, sigma_type x = tau_type x)
(Eq_prog : forall x, sigma_prog x = tau_prog x) (s : prog) {struct s} :
subst_prog sigma_type sigma_prog s = subst_prog tau_type tau_prog s :=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (ext_prog (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_type tau_type) (up_type_prog tau_prog)
           (upExt_type_type _ _ Eq_type) (upExt_type_prog _ _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs (ext_type sigma_type tau_type Eq_type s0)
        (ext_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (upExt_prog_type _ _ Eq_type) (upExt_prog_prog _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s0)
        (ext_type sigma_type tau_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s0)
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s0)
        (ext_prog (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (upExt_prog_type _ _ Eq_type) (upExt_prog_prog _ _ Eq_prog) s1)
  end.

Lemma up_ren_ren_type_prog (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_type_prog zeta) (upRen_type_prog xi) x =
  upRen_type_prog rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_prog_type (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_prog_type zeta) (upRen_prog_type xi) x =
  upRen_prog_type rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_prog_prog (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_prog_prog zeta) (upRen_prog_prog xi) x =
  upRen_prog_prog rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
(zeta_type : nat -> nat) (zeta_prog : nat -> nat) (rho_type : nat -> nat)
(rho_prog : nat -> nat)
(Eq_type : forall x, funcomp zeta_type xi_type x = rho_type x)
(Eq_prog : forall x, funcomp zeta_prog xi_prog x = rho_prog x) (s : prog)
{struct s} :
ren_prog zeta_type zeta_prog (ren_prog xi_type xi_prog s) =
ren_prog rho_type rho_prog s :=
  match s with
  | var_prog s0 => ap (var_prog) (Eq_prog s0)
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (compRenRen_prog (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_type zeta_type) (upRen_type_prog zeta_prog)
           (upRen_type_type rho_type) (upRen_type_prog rho_prog)
           (up_ren_ren _ _ _ Eq_type) Eq_prog s1)
  | tmabs s0 s1 =>
      congr_tmabs (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upRen_prog_type rho_type) (upRen_prog_prog rho_prog) Eq_type
           (up_ren_ren _ _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s0)
        (compRenRen_type xi_type zeta_type rho_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s0)
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s0)
        (compRenRen_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upRen_prog_type rho_type) (upRen_prog_prog rho_prog) Eq_type
           (up_ren_ren _ _ _ Eq_prog) s1)
  end.

Lemma up_ren_subst_type_prog (xi : nat -> nat) (tau : nat -> prog)
  (theta : nat -> prog) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_type_prog tau) (upRen_type_prog xi) x = up_type_prog theta x.
Proof.
exact (fun n => ap (ren_prog shift id) (Eq n)).
Qed.

Lemma up_ren_subst_prog_type (xi : nat -> nat) (tau : nat -> type)
  (theta : nat -> type) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_prog_type tau) (upRen_prog_type xi) x = up_prog_type theta x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma up_ren_subst_prog_prog (xi : nat -> nat) (tau : nat -> prog)
  (theta : nat -> prog) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_prog_prog tau) (upRen_prog_prog xi) x = up_prog_prog theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_prog id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
(tau_type : nat -> type) (tau_prog : nat -> prog) (theta_type : nat -> type)
(theta_prog : nat -> prog)
(Eq_type : forall x, funcomp tau_type xi_type x = theta_type x)
(Eq_prog : forall x, funcomp tau_prog xi_prog x = theta_prog x) (s : prog)
{struct s} :
subst_prog tau_type tau_prog (ren_prog xi_type xi_prog s) =
subst_prog theta_type theta_prog s :=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (compRenSubst_prog (upRen_type_type xi_type)
           (upRen_type_prog xi_prog) (up_type_type tau_type)
           (up_type_prog tau_prog) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_ren_subst_type_type _ _ _ Eq_type)
           (up_ren_subst_type_prog _ _ _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_prog (upRen_prog_type xi_type)
           (upRen_prog_prog xi_prog) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_ren_subst_prog_type _ _ _ Eq_type)
           (up_ren_subst_prog_prog _ _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s0)
        (compRenSubst_type xi_type tau_type theta_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s0)
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s0)
        (compRenSubst_prog (upRen_prog_type xi_type)
           (upRen_prog_prog xi_prog) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_ren_subst_prog_type _ _ _ Eq_type)
           (up_ren_subst_prog_prog _ _ _ Eq_prog) s1)
  end.

Lemma up_subst_ren_type_prog (sigma : nat -> prog) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (theta : nat -> prog)
  (Eq : forall x, funcomp (ren_prog zeta_type zeta_prog) sigma x = theta x) :
  forall x,
  funcomp (ren_prog (upRen_type_type zeta_type) (upRen_type_prog zeta_prog))
    (up_type_prog sigma) x = up_type_prog theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_prog shift id (upRen_type_type zeta_type)
            (upRen_type_prog zeta_prog) (funcomp shift zeta_type)
            (funcomp id zeta_prog) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_prog zeta_type zeta_prog shift id
                  (funcomp shift zeta_type) (funcomp id zeta_prog)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_prog shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_prog_type (sigma : nat -> type) (zeta_type : nat -> nat)
  (theta : nat -> type)
  (Eq : forall x, funcomp (ren_type zeta_type) sigma x = theta x) :
  forall x,
  funcomp (ren_type (upRen_prog_type zeta_type)) (up_prog_type sigma) x =
  up_prog_type theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_type id (upRen_prog_type zeta_type)
            (funcomp id zeta_type) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_type zeta_type id (funcomp id zeta_type)
                  (fun x => eq_refl) (sigma n))) (ap (ren_type id) (Eq n)))).
Qed.

Lemma up_subst_ren_prog_prog (sigma : nat -> prog) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (theta : nat -> prog)
  (Eq : forall x, funcomp (ren_prog zeta_type zeta_prog) sigma x = theta x) :
  forall x,
  funcomp (ren_prog (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog))
    (up_prog_prog sigma) x = up_prog_prog theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_prog id shift (upRen_prog_type zeta_type)
                (upRen_prog_prog zeta_prog) (funcomp id zeta_type)
                (funcomp shift zeta_prog) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_prog zeta_type zeta_prog id shift
                      (funcomp id zeta_type) (funcomp shift zeta_prog)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_prog id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_prog (sigma_type : nat -> type)
(sigma_prog : nat -> prog) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(theta_type : nat -> type) (theta_prog : nat -> prog)
(Eq_type : forall x, funcomp (ren_type zeta_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (ren_prog zeta_type zeta_prog) sigma_prog x = theta_prog x)
(s : prog) {struct s} :
ren_prog zeta_type zeta_prog (subst_prog sigma_type sigma_prog s) =
subst_prog theta_type theta_prog s :=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (compSubstRen_prog (up_type_type sigma_type)
           (up_type_prog sigma_prog) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_subst_ren_type_type _ _ _ Eq_type)
           (up_subst_ren_type_prog _ _ _ _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_prog (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_subst_ren_prog_type _ _ _ Eq_type)
           (up_subst_ren_prog_prog _ _ _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstRen_prog (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_subst_ren_prog_type _ _ _ Eq_type)
           (up_subst_ren_prog_prog _ _ _ _ Eq_prog) s1)
  end.

Lemma up_subst_subst_type_prog (sigma : nat -> prog) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (theta : nat -> prog)
  (Eq : forall x, funcomp (subst_prog tau_type tau_prog) sigma x = theta x) :
  forall x,
  funcomp (subst_prog (up_type_type tau_type) (up_type_prog tau_prog))
    (up_type_prog sigma) x = up_type_prog theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_prog shift id (up_type_type tau_type)
            (up_type_prog tau_prog) (funcomp (up_type_type tau_type) shift)
            (funcomp (up_type_prog tau_prog) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_prog tau_type tau_prog shift id
                  (funcomp (ren_type shift) tau_type)
                  (funcomp (ren_prog shift id) tau_prog) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_prog shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_prog_type (sigma : nat -> type) (tau_type : nat -> type)
  (theta : nat -> type)
  (Eq : forall x, funcomp (subst_type tau_type) sigma x = theta x) :
  forall x,
  funcomp (subst_type (up_prog_type tau_type)) (up_prog_type sigma) x =
  up_prog_type theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_type id (up_prog_type tau_type)
            (funcomp (up_prog_type tau_type) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_type tau_type id
                  (funcomp (ren_type id) tau_type) (fun x => eq_refl)
                  (sigma n))) (ap (ren_type id) (Eq n)))).
Qed.

Lemma up_subst_subst_prog_prog (sigma : nat -> prog) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (theta : nat -> prog)
  (Eq : forall x, funcomp (subst_prog tau_type tau_prog) sigma x = theta x) :
  forall x,
  funcomp (subst_prog (up_prog_type tau_type) (up_prog_prog tau_prog))
    (up_prog_prog sigma) x = up_prog_prog theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_prog id shift (up_prog_type tau_type)
                (up_prog_prog tau_prog) (funcomp (up_prog_type tau_type) id)
                (funcomp (up_prog_prog tau_prog) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_prog tau_type tau_prog id shift
                      (funcomp (ren_type id) tau_type)
                      (funcomp (ren_prog id shift) tau_prog)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_prog id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_prog (sigma_type : nat -> type)
(sigma_prog : nat -> prog) (tau_type : nat -> type) (tau_prog : nat -> prog)
(theta_type : nat -> type) (theta_prog : nat -> prog)
(Eq_type : forall x,
           funcomp (subst_type tau_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (subst_prog tau_type tau_prog) sigma_prog x = theta_prog x)
(s : prog) {struct s} :
subst_prog tau_type tau_prog (subst_prog sigma_type sigma_prog s) =
subst_prog theta_type theta_prog s :=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (compSubstSubst_prog (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_type tau_type)
           (up_type_prog tau_prog) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_subst_subst_type_type _ _ _ Eq_type)
           (up_subst_subst_type_prog _ _ _ _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_prog (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_subst_subst_prog_type _ _ _ Eq_type)
           (up_subst_subst_prog_prog _ _ _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s1)
  | ret s0 =>
      congr_ret
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstSubst_prog (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_subst_subst_prog_type _ _ _ Eq_type)
           (up_subst_subst_prog_prog _ _ _ _ Eq_prog) s1)
  end.

Lemma renRen_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) (s : prog) :
  ren_prog zeta_type zeta_prog (ren_prog xi_type xi_prog s) =
  ren_prog (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog) s.
Proof.
exact (compRenRen_prog xi_type xi_prog zeta_type zeta_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_prog_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_prog zeta_type zeta_prog) (ren_prog xi_type xi_prog))
    (ren_prog (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)).
Proof.
exact (fun s =>
       compRenRen_prog xi_type xi_prog zeta_type zeta_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (tau_type : nat -> type) (tau_prog : nat -> prog) (s : prog) :
  subst_prog tau_type tau_prog (ren_prog xi_type xi_prog s) =
  subst_prog (funcomp tau_type xi_type) (funcomp tau_prog xi_prog) s.
Proof.
exact (compRenSubst_prog xi_type xi_prog tau_type tau_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_prog_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (tau_type : nat -> type) (tau_prog : nat -> prog) :
  pointwise_relation _ eq
    (funcomp (subst_prog tau_type tau_prog) (ren_prog xi_type xi_prog))
    (subst_prog (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)).
Proof.
exact (fun s =>
       compRenSubst_prog xi_type xi_prog tau_type tau_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) (s : prog) :
  ren_prog zeta_type zeta_prog (subst_prog sigma_type sigma_prog s) =
  subst_prog (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog) s.
Proof.
exact (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_prog_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_prog zeta_type zeta_prog)
       (subst_prog sigma_type sigma_prog))
    (subst_prog (funcomp (ren_type zeta_type) sigma_type)
       (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)).
Proof.
exact (fun s =>
       compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (tau_type : nat -> type) (tau_prog : nat -> prog) (s : prog) :
  subst_prog tau_type tau_prog (subst_prog sigma_type sigma_prog s) =
  subst_prog (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog) s.
Proof.
exact (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_prog_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (tau_type : nat -> type)
  (tau_prog : nat -> prog) :
  pointwise_relation _ eq
    (funcomp (subst_prog tau_type tau_prog)
       (subst_prog sigma_type sigma_prog))
    (subst_prog (funcomp (subst_type tau_type) sigma_type)
       (funcomp (subst_prog tau_type tau_prog) sigma_prog)).
Proof.
exact (fun s =>
       compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_type_prog (xi : nat -> nat) (sigma : nat -> prog)
  (Eq : forall x, funcomp (var_prog) xi x = sigma x) :
  forall x, funcomp (var_prog) (upRen_type_prog xi) x = up_type_prog sigma x.
Proof.
exact (fun n => ap (ren_prog shift id) (Eq n)).
Qed.

Lemma rinstInst_up_prog_type (xi : nat -> nat) (sigma : nat -> type)
  (Eq : forall x, funcomp (var_type) xi x = sigma x) :
  forall x, funcomp (var_type) (upRen_prog_type xi) x = up_prog_type sigma x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma rinstInst_up_prog_prog (xi : nat -> nat) (sigma : nat -> prog)
  (Eq : forall x, funcomp (var_prog) xi x = sigma x) :
  forall x, funcomp (var_prog) (upRen_prog_prog xi) x = up_prog_prog sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_prog id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
(sigma_type : nat -> type) (sigma_prog : nat -> prog)
(Eq_type : forall x, funcomp (var_type) xi_type x = sigma_type x)
(Eq_prog : forall x, funcomp (var_prog) xi_prog x = sigma_prog x) (s : prog)
{struct s} : ren_prog xi_type xi_prog s = subst_prog sigma_type sigma_prog s
:=
  match s with
  | var_prog s0 => Eq_prog s0
  | tyabs s0 s1 =>
      congr_tyabs (eq_refl s0)
        (rinst_inst_prog (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (up_type_type sigma_type) (up_type_prog sigma_prog)
           (rinstInst_up_type_type _ _ Eq_type)
           (rinstInst_up_type_prog _ _ Eq_prog) s1)
  | tmabs s0 s1 =>
      congr_tmabs (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (rinstInst_up_prog_type _ _ Eq_type)
           (rinstInst_up_prog_prog _ _ Eq_prog) s1)
  | tyapp s0 s1 =>
      congr_tyapp
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s0) (rinst_inst_type xi_type sigma_type Eq_type s1)
  | tmapp s0 s1 =>
      congr_tmapp
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s0)
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s1)
  | ret s0 =>
      congr_ret
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s0)
  | bind s0 s1 =>
      congr_bind
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s0)
        (rinst_inst_prog (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (rinstInst_up_prog_type _ _ Eq_type)
           (rinstInst_up_prog_prog _ _ Eq_prog) s1)
  end.

Lemma rinstInst'_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (s : prog) :
  ren_prog xi_type xi_prog s =
  subst_prog (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog) s.
Proof.
exact (rinst_inst_prog xi_type xi_prog _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_prog_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  :
  pointwise_relation _ eq (ren_prog xi_type xi_prog)
    (subst_prog (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)).
Proof.
exact (fun s =>
       rinst_inst_prog xi_type xi_prog _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_prog (s : prog) : subst_prog (var_type) (var_prog) s = s.
Proof.
exact (idSubst_prog (var_type) (var_prog) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_prog_pointwise :
  pointwise_relation _ eq (subst_prog (var_type) (var_prog)) id.
Proof.
exact (fun s =>
       idSubst_prog (var_type) (var_prog) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstId'_prog (s : prog) : ren_prog id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_prog s) (rinstInst'_prog id id s)).
Qed.

Lemma rinstId'_prog_pointwise : pointwise_relation _ eq (@ren_prog id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_prog s) (rinstInst'_prog id id s)).
Qed.

Lemma varL'_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (x : nat) : subst_prog sigma_type sigma_prog (var_prog x) = sigma_prog x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_prog_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) :
  pointwise_relation _ eq
    (funcomp (subst_prog sigma_type sigma_prog) (var_prog)) sigma_prog.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_prog (xi_type : nat -> nat) (xi_prog : nat -> nat) (x : nat) :
  ren_prog xi_type xi_prog (var_prog x) = var_prog (xi_prog x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_prog_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_prog xi_type xi_prog) (var_prog))
    (funcomp (var_prog) xi_prog).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive index : Type :=
  | refb : type -> index
  | ref : type -> index -> index
  | univ : nat -> index -> index.

Lemma congr_refb {s0 : type} {t0 : type} (H0 : s0 = t0) : refb s0 = refb t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => refb x) H0)).
Qed.

Lemma congr_ref {s0 : type} {s1 : index} {t0 : type} {t1 : index}
  (H0 : s0 = t0) (H1 : s1 = t1) : ref s0 s1 = ref t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ref x s1) H0))
         (ap (fun x => ref t0 x) H1)).
Qed.

Lemma congr_univ {s0 : nat} {s1 : index} {t0 : nat} {t1 : index}
  (H0 : s0 = t0) (H1 : s1 = t1) : univ s0 s1 = univ t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => univ x s1) H0))
         (ap (fun x => univ t0 x) H1)).
Qed.

Fixpoint ren_index (xi_type : nat -> nat) (s : index) {struct s} : index :=
  match s with
  | refb s0 => refb (ren_type xi_type s0)
  | ref s0 s1 => ref (ren_type xi_type s0) (ren_index xi_type s1)
  | univ s0 s1 => univ s0 (ren_index (upRen_type_type xi_type) s1)
  end.

Fixpoint subst_index (sigma_type : nat -> type) (s : index) {struct s} :
index :=
  match s with
  | refb s0 => refb (subst_type sigma_type s0)
  | ref s0 s1 => ref (subst_type sigma_type s0) (subst_index sigma_type s1)
  | univ s0 s1 => univ s0 (subst_index (up_type_type sigma_type) s1)
  end.

Fixpoint idSubst_index (sigma_type : nat -> type)
(Eq_type : forall x, sigma_type x = var_type x) (s : index) {struct s} :
subst_index sigma_type s = s :=
  match s with
  | refb s0 => congr_refb (idSubst_type sigma_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (idSubst_type sigma_type Eq_type s0)
        (idSubst_index sigma_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (idSubst_index (up_type_type sigma_type) (upId_type_type _ Eq_type)
           s1)
  end.

Fixpoint extRen_index (xi_type : nat -> nat) (zeta_type : nat -> nat)
(Eq_type : forall x, xi_type x = zeta_type x) (s : index) {struct s} :
ren_index xi_type s = ren_index zeta_type s :=
  match s with
  | refb s0 => congr_refb (extRen_type xi_type zeta_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_index xi_type zeta_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (extRen_index (upRen_type_type xi_type) (upRen_type_type zeta_type)
           (upExtRen_type_type _ _ Eq_type) s1)
  end.

Fixpoint ext_index (sigma_type : nat -> type) (tau_type : nat -> type)
(Eq_type : forall x, sigma_type x = tau_type x) (s : index) {struct s} :
subst_index sigma_type s = subst_index tau_type s :=
  match s with
  | refb s0 => congr_refb (ext_type sigma_type tau_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (ext_type sigma_type tau_type Eq_type s0)
        (ext_index sigma_type tau_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (ext_index (up_type_type sigma_type) (up_type_type tau_type)
           (upExt_type_type _ _ Eq_type) s1)
  end.

Fixpoint compRenRen_index (xi_type : nat -> nat) (zeta_type : nat -> nat)
(rho_type : nat -> nat)
(Eq_type : forall x, funcomp zeta_type xi_type x = rho_type x) (s : index)
{struct s} : ren_index zeta_type (ren_index xi_type s) = ren_index rho_type s
:=
  match s with
  | refb s0 =>
      congr_refb (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_index xi_type zeta_type rho_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (compRenRen_index (upRen_type_type xi_type)
           (upRen_type_type zeta_type) (upRen_type_type rho_type)
           (up_ren_ren _ _ _ Eq_type) s1)
  end.

Fixpoint compRenSubst_index (xi_type : nat -> nat) (tau_type : nat -> type)
(theta_type : nat -> type)
(Eq_type : forall x, funcomp tau_type xi_type x = theta_type x) (s : index)
{struct s} :
subst_index tau_type (ren_index xi_type s) = subst_index theta_type s :=
  match s with
  | refb s0 =>
      congr_refb (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_index xi_type tau_type theta_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (compRenSubst_index (upRen_type_type xi_type) (up_type_type tau_type)
           (up_type_type theta_type) (up_ren_subst_type_type _ _ _ Eq_type)
           s1)
  end.

Fixpoint compSubstRen_index (sigma_type : nat -> type)
(zeta_type : nat -> nat) (theta_type : nat -> type)
(Eq_type : forall x, funcomp (ren_type zeta_type) sigma_type x = theta_type x)
(s : index) {struct s} :
ren_index zeta_type (subst_index sigma_type s) = subst_index theta_type s :=
  match s with
  | refb s0 =>
      congr_refb
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_index sigma_type zeta_type theta_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (compSubstRen_index (up_type_type sigma_type)
           (upRen_type_type zeta_type) (up_type_type theta_type)
           (up_subst_ren_type_type _ _ _ Eq_type) s1)
  end.

Fixpoint compSubstSubst_index (sigma_type : nat -> type)
(tau_type : nat -> type) (theta_type : nat -> type)
(Eq_type : forall x,
           funcomp (subst_type tau_type) sigma_type x = theta_type x)
(s : index) {struct s} :
subst_index tau_type (subst_index sigma_type s) = subst_index theta_type s :=
  match s with
  | refb s0 =>
      congr_refb
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_index sigma_type tau_type theta_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (compSubstSubst_index (up_type_type sigma_type)
           (up_type_type tau_type) (up_type_type theta_type)
           (up_subst_subst_type_type _ _ _ Eq_type) s1)
  end.

Lemma renRen_index (xi_type : nat -> nat) (zeta_type : nat -> nat)
  (s : index) :
  ren_index zeta_type (ren_index xi_type s) =
  ren_index (funcomp zeta_type xi_type) s.
Proof.
exact (compRenRen_index xi_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_index_pointwise (xi_type : nat -> nat) (zeta_type : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_index zeta_type) (ren_index xi_type))
    (ren_index (funcomp zeta_type xi_type)).
Proof.
exact (fun s => compRenRen_index xi_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_index (xi_type : nat -> nat) (tau_type : nat -> type)
  (s : index) :
  subst_index tau_type (ren_index xi_type s) =
  subst_index (funcomp tau_type xi_type) s.
Proof.
exact (compRenSubst_index xi_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_index_pointwise (xi_type : nat -> nat)
  (tau_type : nat -> type) :
  pointwise_relation _ eq
    (funcomp (subst_index tau_type) (ren_index xi_type))
    (subst_index (funcomp tau_type xi_type)).
Proof.
exact (fun s => compRenSubst_index xi_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma substRen_index (sigma_type : nat -> type) (zeta_type : nat -> nat)
  (s : index) :
  ren_index zeta_type (subst_index sigma_type s) =
  subst_index (funcomp (ren_type zeta_type) sigma_type) s.
Proof.
exact (compSubstRen_index sigma_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma substRen_index_pointwise (sigma_type : nat -> type)
  (zeta_type : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_index zeta_type) (subst_index sigma_type))
    (subst_index (funcomp (ren_type zeta_type) sigma_type)).
Proof.
exact (fun s =>
       compSubstRen_index sigma_type zeta_type _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_index (sigma_type : nat -> type) (tau_type : nat -> type)
  (s : index) :
  subst_index tau_type (subst_index sigma_type s) =
  subst_index (funcomp (subst_type tau_type) sigma_type) s.
Proof.
exact (compSubstSubst_index sigma_type tau_type _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_index_pointwise (sigma_type : nat -> type)
  (tau_type : nat -> type) :
  pointwise_relation _ eq
    (funcomp (subst_index tau_type) (subst_index sigma_type))
    (subst_index (funcomp (subst_type tau_type) sigma_type)).
Proof.
exact (fun s =>
       compSubstSubst_index sigma_type tau_type _ (fun n => eq_refl) s).
Qed.

Fixpoint rinst_inst_index (xi_type : nat -> nat) (sigma_type : nat -> type)
(Eq_type : forall x, funcomp (var_type) xi_type x = sigma_type x) (s : index)
{struct s} : ren_index xi_type s = subst_index sigma_type s :=
  match s with
  | refb s0 => congr_refb (rinst_inst_type xi_type sigma_type Eq_type s0)
  | ref s0 s1 =>
      congr_ref (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_index xi_type sigma_type Eq_type s1)
  | univ s0 s1 =>
      congr_univ (eq_refl s0)
        (rinst_inst_index (upRen_type_type xi_type) (up_type_type sigma_type)
           (rinstInst_up_type_type _ _ Eq_type) s1)
  end.

Lemma rinstInst'_index (xi_type : nat -> nat) (s : index) :
  ren_index xi_type s = subst_index (funcomp (var_type) xi_type) s.
Proof.
exact (rinst_inst_index xi_type _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_index_pointwise (xi_type : nat -> nat) :
  pointwise_relation _ eq (ren_index xi_type)
    (subst_index (funcomp (var_type) xi_type)).
Proof.
exact (fun s => rinst_inst_index xi_type _ (fun n => eq_refl) s).
Qed.

Lemma instId'_index (s : index) : subst_index (var_type) s = s.
Proof.
exact (idSubst_index (var_type) (fun n => eq_refl) s).
Qed.

Lemma instId'_index_pointwise :
  pointwise_relation _ eq (subst_index (var_type)) id.
Proof.
exact (fun s => idSubst_index (var_type) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_index (s : index) : ren_index id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_index s) (rinstInst'_index id s)).
Qed.

Lemma rinstId'_index_pointwise : pointwise_relation _ eq (@ren_index id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_index s) (rinstInst'_index id s)).
Qed.

Inductive exp : Type :=
  | var_exp : nat -> exp
  | cexp : type -> index -> spec -> exp
  | exabs : nat -> exp -> exp
  | exapp : exp -> type -> exp
with spec : Type :=
  | spholds : exp -> exp -> prog -> spec
  | spimplies : spec -> spec -> spec
  | after : prog -> spec -> spec
  | tyall : nat -> spec -> spec
  | tmall : type -> spec -> spec
  | spall : index -> spec -> spec.

Lemma congr_cexp {s0 : type} {s1 : index} {s2 : spec} {t0 : type}
  {t1 : index} {t2 : spec} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  cexp s0 s1 s2 = cexp t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => cexp x s1 s2) H0))
            (ap (fun x => cexp t0 x s2) H1)) (ap (fun x => cexp t0 t1 x) H2)).
Qed.

Lemma congr_exabs {s0 : nat} {s1 : exp} {t0 : nat} {t1 : exp} (H0 : s0 = t0)
  (H1 : s1 = t1) : exabs s0 s1 = exabs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exabs x s1) H0))
         (ap (fun x => exabs t0 x) H1)).
Qed.

Lemma congr_exapp {s0 : exp} {s1 : type} {t0 : exp} {t1 : type}
  (H0 : s0 = t0) (H1 : s1 = t1) : exapp s0 s1 = exapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exapp x s1) H0))
         (ap (fun x => exapp t0 x) H1)).
Qed.

Lemma congr_spholds {s0 : exp} {s1 : exp} {s2 : prog} {t0 : exp} {t1 : exp}
  {t2 : prog} (H0 : s0 = t0) (H1 : s1 = t1) (H2 : s2 = t2) :
  spholds s0 s1 s2 = spholds t0 t1 t2.
Proof.
exact (eq_trans
         (eq_trans (eq_trans eq_refl (ap (fun x => spholds x s1 s2) H0))
            (ap (fun x => spholds t0 x s2) H1))
         (ap (fun x => spholds t0 t1 x) H2)).
Qed.

Lemma congr_spimplies {s0 : spec} {s1 : spec} {t0 : spec} {t1 : spec}
  (H0 : s0 = t0) (H1 : s1 = t1) : spimplies s0 s1 = spimplies t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => spimplies x s1) H0))
         (ap (fun x => spimplies t0 x) H1)).
Qed.

Lemma congr_after {s0 : prog} {s1 : spec} {t0 : prog} {t1 : spec}
  (H0 : s0 = t0) (H1 : s1 = t1) : after s0 s1 = after t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => after x s1) H0))
         (ap (fun x => after t0 x) H1)).
Qed.

Lemma congr_tyall {s0 : nat} {s1 : spec} {t0 : nat} {t1 : spec}
  (H0 : s0 = t0) (H1 : s1 = t1) : tyall s0 s1 = tyall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tyall x s1) H0))
         (ap (fun x => tyall t0 x) H1)).
Qed.

Lemma congr_tmall {s0 : type} {s1 : spec} {t0 : type} {t1 : spec}
  (H0 : s0 = t0) (H1 : s1 = t1) : tmall s0 s1 = tmall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => tmall x s1) H0))
         (ap (fun x => tmall t0 x) H1)).
Qed.

Lemma congr_spall {s0 : index} {s1 : spec} {t0 : index} {t1 : spec}
  (H0 : s0 = t0) (H1 : s1 = t1) : spall s0 s1 = spall t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => spall x s1) H0))
         (ap (fun x => spall t0 x) H1)).
Qed.

Lemma upRen_type_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_prog_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_exp_type (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_exp_prog (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_exp_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (s : exp) {struct s} : exp :=
  match s with
  | var_exp s0 => var_exp (xi_exp s0)
  | cexp s0 s1 s2 =>
      cexp (ren_type xi_type s0) (ren_index xi_type s1)
        (ren_spec (upRen_prog_type (upRen_exp_type xi_type))
           (upRen_prog_prog (upRen_exp_prog xi_prog))
           (upRen_prog_exp (upRen_exp_exp xi_exp)) s2)
  | exabs s0 s1 =>
      exabs s0
        (ren_exp (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) s1)
  | exapp s0 s1 =>
      exapp (ren_exp xi_type xi_prog xi_exp s0) (ren_type xi_type s1)
  end
with ren_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (s : spec) {struct s} : spec :=
  match s with
  | spholds s0 s1 s2 =>
      spholds (ren_exp xi_type xi_prog xi_exp s0)
        (ren_exp xi_type xi_prog xi_exp s1) (ren_prog xi_type xi_prog s2)
  | spimplies s0 s1 =>
      spimplies (ren_spec xi_type xi_prog xi_exp s0)
        (ren_spec xi_type xi_prog xi_exp s1)
  | after s0 s1 =>
      after (ren_prog xi_type xi_prog s0)
        (ren_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) s1)
  | tyall s0 s1 =>
      tyall s0
        (ren_spec (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) s1)
  | tmall s0 s1 =>
      tmall (ren_type xi_type s0)
        (ren_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) s1)
  | spall s0 s1 =>
      spall (ren_index xi_type s0)
        (ren_spec (upRen_exp_type xi_type) (upRen_exp_prog xi_prog)
           (upRen_exp_exp xi_exp) s1)
  end.

Lemma up_type_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (funcomp (ren_exp shift id id) sigma).
Defined.

Lemma up_prog_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (funcomp (ren_exp id shift id) sigma).
Defined.

Lemma up_exp_type (sigma : nat -> type) : nat -> type.
Proof.
exact (funcomp (ren_type id) sigma).
Defined.

Lemma up_exp_prog (sigma : nat -> prog) : nat -> prog.
Proof.
exact (funcomp (ren_prog id id) sigma).
Defined.

Lemma up_exp_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (scons (var_exp var_zero) (funcomp (ren_exp id id shift) sigma)).
Defined.

Fixpoint subst_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (s : exp) {struct s} : exp :=
  match s with
  | var_exp s0 => sigma_exp s0
  | cexp s0 s1 s2 =>
      cexp (subst_type sigma_type s0) (subst_index sigma_type s1)
        (subst_spec (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp)) s2)
  | exabs s0 s1 =>
      exabs s0
        (subst_exp (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) s1)
  | exapp s0 s1 =>
      exapp (subst_exp sigma_type sigma_prog sigma_exp s0)
        (subst_type sigma_type s1)
  end
with subst_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (s : spec) {struct s} : spec :=
  match s with
  | spholds s0 s1 s2 =>
      spholds (subst_exp sigma_type sigma_prog sigma_exp s0)
        (subst_exp sigma_type sigma_prog sigma_exp s1)
        (subst_prog sigma_type sigma_prog s2)
  | spimplies s0 s1 =>
      spimplies (subst_spec sigma_type sigma_prog sigma_exp s0)
        (subst_spec sigma_type sigma_prog sigma_exp s1)
  | after s0 s1 =>
      after (subst_prog sigma_type sigma_prog s0)
        (subst_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) s1)
  | tyall s0 s1 =>
      tyall s0
        (subst_spec (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) s1)
  | tmall s0 s1 =>
      tmall (subst_type sigma_type s0)
        (subst_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) s1)
  | spall s0 s1 =>
      spall (subst_index sigma_type s0)
        (subst_spec (up_exp_type sigma_type) (up_exp_prog sigma_prog)
           (up_exp_exp sigma_exp) s1)
  end.

Lemma upId_type_exp (sigma : nat -> exp) (Eq : forall x, sigma x = var_exp x)
  : forall x, up_type_exp sigma x = var_exp x.
Proof.
exact (fun n => ap (ren_exp shift id id) (Eq n)).
Qed.

Lemma upId_prog_exp (sigma : nat -> exp) (Eq : forall x, sigma x = var_exp x)
  : forall x, up_prog_exp sigma x = var_exp x.
Proof.
exact (fun n => ap (ren_exp id shift id) (Eq n)).
Qed.

Lemma upId_exp_type (sigma : nat -> type)
  (Eq : forall x, sigma x = var_type x) :
  forall x, up_exp_type sigma x = var_type x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma upId_exp_prog (sigma : nat -> prog)
  (Eq : forall x, sigma x = var_prog x) :
  forall x, up_exp_prog sigma x = var_prog x.
Proof.
exact (fun n => ap (ren_prog id id) (Eq n)).
Qed.

Lemma upId_exp_exp (sigma : nat -> exp) (Eq : forall x, sigma x = var_exp x)
  : forall x, up_exp_exp sigma x = var_exp x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (Eq_type : forall x, sigma_type x = var_type x)
(Eq_prog : forall x, sigma_prog x = var_prog x)
(Eq_exp : forall x, sigma_exp x = var_exp x) (s : exp) {struct s} :
subst_exp sigma_type sigma_prog sigma_exp s = s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp (idSubst_type sigma_type Eq_type s0)
        (idSubst_index sigma_type Eq_type s1)
        (idSubst_spec (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp))
           (upId_prog_type _ (upId_exp_type _ Eq_type))
           (upId_prog_prog _ (upId_exp_prog _ Eq_prog))
           (upId_prog_exp _ (upId_exp_exp _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (idSubst_exp (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) (upId_type_type _ Eq_type)
           (upId_type_prog _ Eq_prog) (upId_type_exp _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (idSubst_exp sigma_type sigma_prog sigma_exp Eq_type Eq_prog Eq_exp
           s0) (idSubst_type sigma_type Eq_type s1)
  end
with idSubst_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (Eq_type : forall x, sigma_type x = var_type x)
(Eq_prog : forall x, sigma_prog x = var_prog x)
(Eq_exp : forall x, sigma_exp x = var_exp x) (s : spec) {struct s} :
subst_spec sigma_type sigma_prog sigma_exp s = s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (idSubst_exp sigma_type sigma_prog sigma_exp Eq_type Eq_prog Eq_exp
           s0)
        (idSubst_exp sigma_type sigma_prog sigma_exp Eq_type Eq_prog Eq_exp
           s1) (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (idSubst_spec sigma_type sigma_prog sigma_exp Eq_type Eq_prog Eq_exp
           s0)
        (idSubst_spec sigma_type sigma_prog sigma_exp Eq_type Eq_prog Eq_exp
           s1)
  | after s0 s1 =>
      congr_after (idSubst_prog sigma_type sigma_prog Eq_type Eq_prog s0)
        (idSubst_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) (upId_prog_type _ Eq_type)
           (upId_prog_prog _ Eq_prog) (upId_prog_exp _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (idSubst_spec (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) (upId_type_type _ Eq_type)
           (upId_type_prog _ Eq_prog) (upId_type_exp _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall (idSubst_type sigma_type Eq_type s0)
        (idSubst_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) (upId_prog_type _ Eq_type)
           (upId_prog_prog _ Eq_prog) (upId_prog_exp _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall (idSubst_index sigma_type Eq_type s0)
        (idSubst_spec (up_exp_type sigma_type) (up_exp_prog sigma_prog)
           (up_exp_exp sigma_exp) (upId_exp_type _ Eq_type)
           (upId_exp_prog _ Eq_prog) (upId_exp_exp _ Eq_exp) s1)
  end.

Lemma upExtRen_type_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_type_exp xi x = upRen_type_exp zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_prog_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_prog_exp xi x = upRen_prog_exp zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_exp_type (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_type xi x = upRen_exp_type zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_exp_prog (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_prog xi x = upRen_exp_prog zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_exp xi x = upRen_exp_exp zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(zeta_exp : nat -> nat) (Eq_type : forall x, xi_type x = zeta_type x)
(Eq_prog : forall x, xi_prog x = zeta_prog x)
(Eq_exp : forall x, xi_exp x = zeta_exp x) (s : exp) {struct s} :
ren_exp xi_type xi_prog xi_exp s = ren_exp zeta_type zeta_prog zeta_exp s :=
  match s with
  | var_exp s0 => ap (var_exp) (Eq_exp s0)
  | cexp s0 s1 s2 =>
      congr_cexp (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_index xi_type zeta_type Eq_type s1)
        (extRen_spec (upRen_prog_type (upRen_exp_type xi_type))
           (upRen_prog_prog (upRen_exp_prog xi_prog))
           (upRen_prog_exp (upRen_exp_exp xi_exp))
           (upRen_prog_type (upRen_exp_type zeta_type))
           (upRen_prog_prog (upRen_exp_prog zeta_prog))
           (upRen_prog_exp (upRen_exp_exp zeta_exp))
           (upExtRen_prog_type _ _ (upExtRen_exp_type _ _ Eq_type))
           (upExtRen_prog_prog _ _ (upExtRen_exp_prog _ _ Eq_prog))
           (upExtRen_prog_exp _ _ (upExtRen_exp_exp _ _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (extRen_exp (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
           (upExtRen_type_type _ _ Eq_type) (upExtRen_type_prog _ _ Eq_prog)
           (upExtRen_type_exp _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (extRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           Eq_type Eq_prog Eq_exp s0)
        (extRen_type xi_type zeta_type Eq_type s1)
  end
with extRen_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(zeta_exp : nat -> nat) (Eq_type : forall x, xi_type x = zeta_type x)
(Eq_prog : forall x, xi_prog x = zeta_prog x)
(Eq_exp : forall x, xi_exp x = zeta_exp x) (s : spec) {struct s} :
ren_spec xi_type xi_prog xi_exp s = ren_spec zeta_type zeta_prog zeta_exp s
:=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (extRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           Eq_type Eq_prog Eq_exp s0)
        (extRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           Eq_type Eq_prog Eq_exp s1)
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (extRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           Eq_type Eq_prog Eq_exp s0)
        (extRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           Eq_type Eq_prog Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (extRen_prog xi_type xi_prog zeta_type zeta_prog Eq_type Eq_prog s0)
        (extRen_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (upRen_prog_exp zeta_exp)
           (upExtRen_prog_type _ _ Eq_type) (upExtRen_prog_prog _ _ Eq_prog)
           (upExtRen_prog_exp _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (extRen_spec (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
           (upExtRen_type_type _ _ Eq_type) (upExtRen_type_prog _ _ Eq_prog)
           (upExtRen_type_exp _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall (extRen_type xi_type zeta_type Eq_type s0)
        (extRen_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (upRen_prog_exp zeta_exp)
           (upExtRen_prog_type _ _ Eq_type) (upExtRen_prog_prog _ _ Eq_prog)
           (upExtRen_prog_exp _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall (extRen_index xi_type zeta_type Eq_type s0)
        (extRen_spec (upRen_exp_type xi_type) (upRen_exp_prog xi_prog)
           (upRen_exp_exp xi_exp) (upRen_exp_type zeta_type)
           (upRen_exp_prog zeta_prog) (upRen_exp_exp zeta_exp)
           (upExtRen_exp_type _ _ Eq_type) (upExtRen_exp_prog _ _ Eq_prog)
           (upExtRen_exp_exp _ _ Eq_exp) s1)
  end.

Lemma upExt_type_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_type_exp sigma x = up_type_exp tau x.
Proof.
exact (fun n => ap (ren_exp shift id id) (Eq n)).
Qed.

Lemma upExt_prog_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_prog_exp sigma x = up_prog_exp tau x.
Proof.
exact (fun n => ap (ren_exp id shift id) (Eq n)).
Qed.

Lemma upExt_exp_type (sigma : nat -> type) (tau : nat -> type)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_type sigma x = up_exp_type tau x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma upExt_exp_prog (sigma : nat -> prog) (tau : nat -> prog)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_prog sigma x = up_exp_prog tau x.
Proof.
exact (fun n => ap (ren_prog id id) (Eq n)).
Qed.

Lemma upExt_exp_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_exp sigma x = up_exp_exp tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
(tau_exp : nat -> exp) (Eq_type : forall x, sigma_type x = tau_type x)
(Eq_prog : forall x, sigma_prog x = tau_prog x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : exp) {struct s} :
subst_exp sigma_type sigma_prog sigma_exp s =
subst_exp tau_type tau_prog tau_exp s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp (ext_type sigma_type tau_type Eq_type s0)
        (ext_index sigma_type tau_type Eq_type s1)
        (ext_spec (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp))
           (up_prog_type (up_exp_type tau_type))
           (up_prog_prog (up_exp_prog tau_prog))
           (up_prog_exp (up_exp_exp tau_exp))
           (upExt_prog_type _ _ (upExt_exp_type _ _ Eq_type))
           (upExt_prog_prog _ _ (upExt_exp_prog _ _ Eq_prog))
           (upExt_prog_exp _ _ (upExt_exp_exp _ _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (ext_exp (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) (up_type_type tau_type)
           (up_type_prog tau_prog) (up_type_exp tau_exp)
           (upExt_type_type _ _ Eq_type) (upExt_type_prog _ _ Eq_prog)
           (upExt_type_exp _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (ext_exp sigma_type sigma_prog sigma_exp tau_type tau_prog tau_exp
           Eq_type Eq_prog Eq_exp s0)
        (ext_type sigma_type tau_type Eq_type s1)
  end
with ext_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
(tau_exp : nat -> exp) (Eq_type : forall x, sigma_type x = tau_type x)
(Eq_prog : forall x, sigma_prog x = tau_prog x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : spec) {struct s} :
subst_spec sigma_type sigma_prog sigma_exp s =
subst_spec tau_type tau_prog tau_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (ext_exp sigma_type sigma_prog sigma_exp tau_type tau_prog tau_exp
           Eq_type Eq_prog Eq_exp s0)
        (ext_exp sigma_type sigma_prog sigma_exp tau_type tau_prog tau_exp
           Eq_type Eq_prog Eq_exp s1)
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (ext_spec sigma_type sigma_prog sigma_exp tau_type tau_prog tau_exp
           Eq_type Eq_prog Eq_exp s0)
        (ext_spec sigma_type sigma_prog sigma_exp tau_type tau_prog tau_exp
           Eq_type Eq_prog Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (ext_prog sigma_type sigma_prog tau_type tau_prog Eq_type Eq_prog s0)
        (ext_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_exp tau_exp)
           (upExt_prog_type _ _ Eq_type) (upExt_prog_prog _ _ Eq_prog)
           (upExt_prog_exp _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (ext_spec (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) (up_type_type tau_type)
           (up_type_prog tau_prog) (up_type_exp tau_exp)
           (upExt_type_type _ _ Eq_type) (upExt_type_prog _ _ Eq_prog)
           (upExt_type_exp _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall (ext_type sigma_type tau_type Eq_type s0)
        (ext_spec (up_prog_type sigma_type) (up_prog_prog sigma_prog)
           (up_prog_exp sigma_exp) (up_prog_type tau_type)
           (up_prog_prog tau_prog) (up_prog_exp tau_exp)
           (upExt_prog_type _ _ Eq_type) (upExt_prog_prog _ _ Eq_prog)
           (upExt_prog_exp _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall (ext_index sigma_type tau_type Eq_type s0)
        (ext_spec (up_exp_type sigma_type) (up_exp_prog sigma_prog)
           (up_exp_exp sigma_exp) (up_exp_type tau_type)
           (up_exp_prog tau_prog) (up_exp_exp tau_exp)
           (upExt_exp_type _ _ Eq_type) (upExt_exp_prog _ _ Eq_prog)
           (upExt_exp_exp _ _ Eq_exp) s1)
  end.

Lemma up_ren_ren_type_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_type_exp zeta) (upRen_type_exp xi) x = upRen_type_exp rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_prog_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_prog_exp zeta) (upRen_prog_exp xi) x = upRen_prog_exp rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_exp_type (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_type zeta) (upRen_exp_type xi) x = upRen_exp_type rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_exp_prog (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_prog zeta) (upRen_exp_prog xi) x = upRen_exp_prog rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_exp zeta) (upRen_exp_exp xi) x = upRen_exp_exp rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(zeta_exp : nat -> nat) (rho_type : nat -> nat) (rho_prog : nat -> nat)
(rho_exp : nat -> nat)
(Eq_type : forall x, funcomp zeta_type xi_type x = rho_type x)
(Eq_prog : forall x, funcomp zeta_prog xi_prog x = rho_prog x)
(Eq_exp : forall x, funcomp zeta_exp xi_exp x = rho_exp x) (s : exp) {struct
 s} :
ren_exp zeta_type zeta_prog zeta_exp (ren_exp xi_type xi_prog xi_exp s) =
ren_exp rho_type rho_prog rho_exp s :=
  match s with
  | var_exp s0 => ap (var_exp) (Eq_exp s0)
  | cexp s0 s1 s2 =>
      congr_cexp (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_index xi_type zeta_type rho_type Eq_type s1)
        (compRenRen_spec (upRen_prog_type (upRen_exp_type xi_type))
           (upRen_prog_prog (upRen_exp_prog xi_prog))
           (upRen_prog_exp (upRen_exp_exp xi_exp))
           (upRen_prog_type (upRen_exp_type zeta_type))
           (upRen_prog_prog (upRen_exp_prog zeta_prog))
           (upRen_prog_exp (upRen_exp_exp zeta_exp))
           (upRen_prog_type (upRen_exp_type rho_type))
           (upRen_prog_prog (upRen_exp_prog rho_prog))
           (upRen_prog_exp (upRen_exp_exp rho_exp)) Eq_type
           (up_ren_ren _ _ _ Eq_prog) (up_ren_ren _ _ _ Eq_exp) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (compRenRen_exp (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
           (upRen_type_type rho_type) (upRen_type_prog rho_prog)
           (upRen_type_exp rho_exp) (up_ren_ren _ _ _ Eq_type) Eq_prog Eq_exp
           s1)
  | exapp s0 s1 =>
      congr_exapp
        (compRenRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           rho_type rho_prog rho_exp Eq_type Eq_prog Eq_exp s0)
        (compRenRen_type xi_type zeta_type rho_type Eq_type s1)
  end
with compRenRen_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(zeta_exp : nat -> nat) (rho_type : nat -> nat) (rho_prog : nat -> nat)
(rho_exp : nat -> nat)
(Eq_type : forall x, funcomp zeta_type xi_type x = rho_type x)
(Eq_prog : forall x, funcomp zeta_prog xi_prog x = rho_prog x)
(Eq_exp : forall x, funcomp zeta_exp xi_exp x = rho_exp x) (s : spec) {struct
 s} :
ren_spec zeta_type zeta_prog zeta_exp (ren_spec xi_type xi_prog xi_exp s) =
ren_spec rho_type rho_prog rho_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (compRenRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           rho_type rho_prog rho_exp Eq_type Eq_prog Eq_exp s0)
        (compRenRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           rho_type rho_prog rho_exp Eq_type Eq_prog Eq_exp s1)
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (compRenRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           rho_type rho_prog rho_exp Eq_type Eq_prog Eq_exp s0)
        (compRenRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp
           rho_type rho_prog rho_exp Eq_type Eq_prog Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (compRenRen_prog xi_type xi_prog zeta_type zeta_prog rho_type
           rho_prog Eq_type Eq_prog s0)
        (compRenRen_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (upRen_prog_exp zeta_exp)
           (upRen_prog_type rho_type) (upRen_prog_prog rho_prog)
           (upRen_prog_exp rho_exp) Eq_type (up_ren_ren _ _ _ Eq_prog) Eq_exp
           s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (compRenRen_spec (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
           (upRen_type_type rho_type) (upRen_type_prog rho_prog)
           (upRen_type_exp rho_exp) (up_ren_ren _ _ _ Eq_type) Eq_prog Eq_exp
           s1)
  | tmall s0 s1 =>
      congr_tmall (compRenRen_type xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (upRen_prog_type zeta_type)
           (upRen_prog_prog zeta_prog) (upRen_prog_exp zeta_exp)
           (upRen_prog_type rho_type) (upRen_prog_prog rho_prog)
           (upRen_prog_exp rho_exp) Eq_type (up_ren_ren _ _ _ Eq_prog) Eq_exp
           s1)
  | spall s0 s1 =>
      congr_spall (compRenRen_index xi_type zeta_type rho_type Eq_type s0)
        (compRenRen_spec (upRen_exp_type xi_type) (upRen_exp_prog xi_prog)
           (upRen_exp_exp xi_exp) (upRen_exp_type zeta_type)
           (upRen_exp_prog zeta_prog) (upRen_exp_exp zeta_exp)
           (upRen_exp_type rho_type) (upRen_exp_prog rho_prog)
           (upRen_exp_exp rho_exp) Eq_type Eq_prog (up_ren_ren _ _ _ Eq_exp)
           s1)
  end.

Lemma up_ren_subst_type_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_type_exp tau) (upRen_type_exp xi) x = up_type_exp theta x.
Proof.
exact (fun n => ap (ren_exp shift id id) (Eq n)).
Qed.

Lemma up_ren_subst_prog_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_prog_exp tau) (upRen_prog_exp xi) x = up_prog_exp theta x.
Proof.
exact (fun n => ap (ren_exp id shift id) (Eq n)).
Qed.

Lemma up_ren_subst_exp_type (xi : nat -> nat) (tau : nat -> type)
  (theta : nat -> type) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_type tau) (upRen_exp_type xi) x = up_exp_type theta x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma up_ren_subst_exp_prog (xi : nat -> nat) (tau : nat -> prog)
  (theta : nat -> prog) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_prog tau) (upRen_exp_prog xi) x = up_exp_prog theta x.
Proof.
exact (fun n => ap (ren_prog id id) (Eq n)).
Qed.

Lemma up_ren_subst_exp_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_exp tau) (upRen_exp_exp xi) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
(tau_exp : nat -> exp) (theta_type : nat -> type) (theta_prog : nat -> prog)
(theta_exp : nat -> exp)
(Eq_type : forall x, funcomp tau_type xi_type x = theta_type x)
(Eq_prog : forall x, funcomp tau_prog xi_prog x = theta_prog x)
(Eq_exp : forall x, funcomp tau_exp xi_exp x = theta_exp x) (s : exp) {struct
 s} :
subst_exp tau_type tau_prog tau_exp (ren_exp xi_type xi_prog xi_exp s) =
subst_exp theta_type theta_prog theta_exp s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_index xi_type tau_type theta_type Eq_type s1)
        (compRenSubst_spec (upRen_prog_type (upRen_exp_type xi_type))
           (upRen_prog_prog (upRen_exp_prog xi_prog))
           (upRen_prog_exp (upRen_exp_exp xi_exp))
           (up_prog_type (up_exp_type tau_type))
           (up_prog_prog (up_exp_prog tau_prog))
           (up_prog_exp (up_exp_exp tau_exp))
           (up_prog_type (up_exp_type theta_type))
           (up_prog_prog (up_exp_prog theta_prog))
           (up_prog_exp (up_exp_exp theta_exp))
           (up_ren_subst_prog_type _ _ _
              (up_ren_subst_exp_type _ _ _ Eq_type))
           (up_ren_subst_prog_prog _ _ _
              (up_ren_subst_exp_prog _ _ _ Eq_prog))
           (up_ren_subst_prog_exp _ _ _ (up_ren_subst_exp_exp _ _ _ Eq_exp))
           s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (compRenSubst_exp (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (up_type_type tau_type)
           (up_type_prog tau_prog) (up_type_exp tau_exp)
           (up_type_type theta_type) (up_type_prog theta_prog)
           (up_type_exp theta_exp) (up_ren_subst_type_type _ _ _ Eq_type)
           (up_ren_subst_type_prog _ _ _ Eq_prog)
           (up_ren_subst_type_exp _ _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (compRenSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp
           theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compRenSubst_type xi_type tau_type theta_type Eq_type s1)
  end
with compRenSubst_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
(tau_exp : nat -> exp) (theta_type : nat -> type) (theta_prog : nat -> prog)
(theta_exp : nat -> exp)
(Eq_type : forall x, funcomp tau_type xi_type x = theta_type x)
(Eq_prog : forall x, funcomp tau_prog xi_prog x = theta_prog x)
(Eq_exp : forall x, funcomp tau_exp xi_exp x = theta_exp x) (s : spec)
{struct s} :
subst_spec tau_type tau_prog tau_exp (ren_spec xi_type xi_prog xi_exp s) =
subst_spec theta_type theta_prog theta_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (compRenSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp
           theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compRenSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp
           theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s1)
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (compRenSubst_spec xi_type xi_prog xi_exp tau_type tau_prog tau_exp
           theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compRenSubst_spec xi_type xi_prog xi_exp tau_type tau_prog tau_exp
           theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (compRenSubst_prog xi_type xi_prog tau_type tau_prog theta_type
           theta_prog Eq_type Eq_prog s0)
        (compRenSubst_spec (upRen_prog_type xi_type)
           (upRen_prog_prog xi_prog) (upRen_prog_exp xi_exp)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (up_prog_exp tau_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_ren_subst_prog_type _ _ _ Eq_type)
           (up_ren_subst_prog_prog _ _ _ Eq_prog)
           (up_ren_subst_prog_exp _ _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (compRenSubst_spec (upRen_type_type xi_type)
           (upRen_type_prog xi_prog) (upRen_type_exp xi_exp)
           (up_type_type tau_type) (up_type_prog tau_prog)
           (up_type_exp tau_exp) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_type_exp theta_exp)
           (up_ren_subst_type_type _ _ _ Eq_type)
           (up_ren_subst_type_prog _ _ _ Eq_prog)
           (up_ren_subst_type_exp _ _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall (compRenSubst_type xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_spec (upRen_prog_type xi_type)
           (upRen_prog_prog xi_prog) (upRen_prog_exp xi_exp)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (up_prog_exp tau_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_ren_subst_prog_type _ _ _ Eq_type)
           (up_ren_subst_prog_prog _ _ _ Eq_prog)
           (up_ren_subst_prog_exp _ _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall (compRenSubst_index xi_type tau_type theta_type Eq_type s0)
        (compRenSubst_spec (upRen_exp_type xi_type) (upRen_exp_prog xi_prog)
           (upRen_exp_exp xi_exp) (up_exp_type tau_type)
           (up_exp_prog tau_prog) (up_exp_exp tau_exp)
           (up_exp_type theta_type) (up_exp_prog theta_prog)
           (up_exp_exp theta_exp) (up_ren_subst_exp_type _ _ _ Eq_type)
           (up_ren_subst_exp_prog _ _ _ Eq_prog)
           (up_ren_subst_exp_exp _ _ _ Eq_exp) s1)
  end.

Lemma up_subst_ren_type_exp (sigma : nat -> exp) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (zeta_exp : nat -> nat) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma x = theta x) :
  forall x,
  funcomp
    (ren_exp (upRen_type_type zeta_type) (upRen_type_prog zeta_prog)
       (upRen_type_exp zeta_exp)) (up_type_exp sigma) x = up_type_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_exp shift id id (upRen_type_type zeta_type)
            (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
            (funcomp shift zeta_type) (funcomp id zeta_prog)
            (funcomp id zeta_exp) (fun x => eq_refl) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_exp zeta_type zeta_prog zeta_exp shift id id
                  (funcomp shift zeta_type) (funcomp id zeta_prog)
                  (funcomp id zeta_exp) (fun x => eq_refl) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_exp shift id id) (Eq n)))).
Qed.

Lemma up_subst_ren_prog_exp (sigma : nat -> exp) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (zeta_exp : nat -> nat) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma x = theta x) :
  forall x,
  funcomp
    (ren_exp (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
       (upRen_prog_exp zeta_exp)) (up_prog_exp sigma) x = up_prog_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_exp id shift id (upRen_prog_type zeta_type)
            (upRen_prog_prog zeta_prog) (upRen_prog_exp zeta_exp)
            (funcomp id zeta_type) (funcomp shift zeta_prog)
            (funcomp id zeta_exp) (fun x => eq_refl) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_exp zeta_type zeta_prog zeta_exp id shift id
                  (funcomp id zeta_type) (funcomp shift zeta_prog)
                  (funcomp id zeta_exp) (fun x => eq_refl) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_exp id shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_exp_type (sigma : nat -> type) (zeta_type : nat -> nat)
  (theta : nat -> type)
  (Eq : forall x, funcomp (ren_type zeta_type) sigma x = theta x) :
  forall x,
  funcomp (ren_type (upRen_exp_type zeta_type)) (up_exp_type sigma) x =
  up_exp_type theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_type id (upRen_exp_type zeta_type)
            (funcomp id zeta_type) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_type zeta_type id (funcomp id zeta_type)
                  (fun x => eq_refl) (sigma n))) (ap (ren_type id) (Eq n)))).
Qed.

Lemma up_subst_ren_exp_prog (sigma : nat -> prog) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (theta : nat -> prog)
  (Eq : forall x, funcomp (ren_prog zeta_type zeta_prog) sigma x = theta x) :
  forall x,
  funcomp (ren_prog (upRen_exp_type zeta_type) (upRen_exp_prog zeta_prog))
    (up_exp_prog sigma) x = up_exp_prog theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_prog id id (upRen_exp_type zeta_type)
            (upRen_exp_prog zeta_prog) (funcomp id zeta_type)
            (funcomp id zeta_prog) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_prog zeta_type zeta_prog id id
                  (funcomp id zeta_type) (funcomp id zeta_prog)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_prog id id) (Eq n)))).
Qed.

Lemma up_subst_ren_exp_exp (sigma : nat -> exp) (zeta_type : nat -> nat)
  (zeta_prog : nat -> nat) (zeta_exp : nat -> nat) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma x = theta x) :
  forall x,
  funcomp
    (ren_exp (upRen_exp_type zeta_type) (upRen_exp_prog zeta_prog)
       (upRen_exp_exp zeta_exp)) (up_exp_exp sigma) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_exp id id shift (upRen_exp_type zeta_type)
                (upRen_exp_prog zeta_prog) (upRen_exp_exp zeta_exp)
                (funcomp id zeta_type) (funcomp id zeta_prog)
                (funcomp shift zeta_exp) (fun x => eq_refl)
                (fun x => eq_refl) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_exp zeta_type zeta_prog zeta_exp id id shift
                      (funcomp id zeta_type) (funcomp id zeta_prog)
                      (funcomp shift zeta_exp) (fun x => eq_refl)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_exp id id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_exp (sigma_type : nat -> type)
(sigma_prog : nat -> prog) (sigma_exp : nat -> exp) (zeta_type : nat -> nat)
(zeta_prog : nat -> nat) (zeta_exp : nat -> nat) (theta_type : nat -> type)
(theta_prog : nat -> prog) (theta_exp : nat -> exp)
(Eq_type : forall x, funcomp (ren_type zeta_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (ren_prog zeta_type zeta_prog) sigma_prog x = theta_prog x)
(Eq_exp : forall x,
          funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp x =
          theta_exp x) (s : exp) {struct s} :
ren_exp zeta_type zeta_prog zeta_exp
  (subst_exp sigma_type sigma_prog sigma_exp s) =
subst_exp theta_type theta_prog theta_exp s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_index sigma_type zeta_type theta_type Eq_type s1)
        (compSubstRen_spec (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp))
           (upRen_prog_type (upRen_exp_type zeta_type))
           (upRen_prog_prog (upRen_exp_prog zeta_prog))
           (upRen_prog_exp (upRen_exp_exp zeta_exp))
           (up_prog_type (up_exp_type theta_type))
           (up_prog_prog (up_exp_prog theta_prog))
           (up_prog_exp (up_exp_exp theta_exp))
           (up_subst_ren_prog_type _ _ _
              (up_subst_ren_exp_type _ _ _ Eq_type))
           (up_subst_ren_prog_prog _ _ _ _
              (up_subst_ren_exp_prog _ _ _ _ Eq_prog))
           (up_subst_ren_prog_exp _ _ _ _ _
              (up_subst_ren_exp_exp _ _ _ _ _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (compSubstRen_exp (up_type_type sigma_type) (up_type_prog sigma_prog)
           (up_type_exp sigma_exp) (upRen_type_type zeta_type)
           (upRen_type_prog zeta_prog) (upRen_type_exp zeta_exp)
           (up_type_type theta_type) (up_type_prog theta_prog)
           (up_type_exp theta_exp) (up_subst_ren_type_type _ _ _ Eq_type)
           (up_subst_ren_type_prog _ _ _ _ Eq_prog)
           (up_subst_ren_type_exp _ _ _ _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (compSubstRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
           zeta_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s1)
  end
with compSubstRen_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
(zeta_exp : nat -> nat) (theta_type : nat -> type) (theta_prog : nat -> prog)
(theta_exp : nat -> exp)
(Eq_type : forall x, funcomp (ren_type zeta_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (ren_prog zeta_type zeta_prog) sigma_prog x = theta_prog x)
(Eq_exp : forall x,
          funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp x =
          theta_exp x) (s : spec) {struct s} :
ren_spec zeta_type zeta_prog zeta_exp
  (subst_spec sigma_type sigma_prog sigma_exp s) =
subst_spec theta_type theta_prog theta_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (compSubstRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
           zeta_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compSubstRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
           zeta_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s1)
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (compSubstRen_spec sigma_type sigma_prog sigma_exp zeta_type
           zeta_prog zeta_exp theta_type theta_prog theta_exp Eq_type Eq_prog
           Eq_exp s0)
        (compSubstRen_spec sigma_type sigma_prog sigma_exp zeta_type
           zeta_prog zeta_exp theta_type theta_prog theta_exp Eq_type Eq_prog
           Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (compSubstRen_prog sigma_type sigma_prog zeta_type zeta_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstRen_spec (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upRen_prog_exp zeta_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_subst_ren_prog_type _ _ _ Eq_type)
           (up_subst_ren_prog_prog _ _ _ _ Eq_prog)
           (up_subst_ren_prog_exp _ _ _ _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (compSubstRen_spec (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_exp sigma_exp)
           (upRen_type_type zeta_type) (upRen_type_prog zeta_prog)
           (upRen_type_exp zeta_exp) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_type_exp theta_exp)
           (up_subst_ren_type_type _ _ _ Eq_type)
           (up_subst_ren_type_prog _ _ _ _ Eq_prog)
           (up_subst_ren_type_exp _ _ _ _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall
        (compSubstRen_type sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_spec (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (upRen_prog_type zeta_type) (upRen_prog_prog zeta_prog)
           (upRen_prog_exp zeta_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_subst_ren_prog_type _ _ _ Eq_type)
           (up_subst_ren_prog_prog _ _ _ _ Eq_prog)
           (up_subst_ren_prog_exp _ _ _ _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall
        (compSubstRen_index sigma_type zeta_type theta_type Eq_type s0)
        (compSubstRen_spec (up_exp_type sigma_type) (up_exp_prog sigma_prog)
           (up_exp_exp sigma_exp) (upRen_exp_type zeta_type)
           (upRen_exp_prog zeta_prog) (upRen_exp_exp zeta_exp)
           (up_exp_type theta_type) (up_exp_prog theta_prog)
           (up_exp_exp theta_exp) (up_subst_ren_exp_type _ _ _ Eq_type)
           (up_subst_ren_exp_prog _ _ _ _ Eq_prog)
           (up_subst_ren_exp_exp _ _ _ _ _ Eq_exp) s1)
  end.

Lemma up_subst_subst_type_exp (sigma : nat -> exp) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (tau_exp : nat -> exp) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (subst_exp tau_type tau_prog tau_exp) sigma x = theta x) :
  forall x,
  funcomp
    (subst_exp (up_type_type tau_type) (up_type_prog tau_prog)
       (up_type_exp tau_exp)) (up_type_exp sigma) x = up_type_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_exp shift id id (up_type_type tau_type)
            (up_type_prog tau_prog) (up_type_exp tau_exp)
            (funcomp (up_type_type tau_type) shift)
            (funcomp (up_type_prog tau_prog) id)
            (funcomp (up_type_exp tau_exp) id) (fun x => eq_refl)
            (fun x => eq_refl) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_exp tau_type tau_prog tau_exp shift id id
                  (funcomp (ren_type shift) tau_type)
                  (funcomp (ren_prog shift id) tau_prog)
                  (funcomp (ren_exp shift id id) tau_exp) (fun x => eq_refl)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_exp shift id id) (Eq n)))).
Qed.

Lemma up_subst_subst_prog_exp (sigma : nat -> exp) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (tau_exp : nat -> exp) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (subst_exp tau_type tau_prog tau_exp) sigma x = theta x) :
  forall x,
  funcomp
    (subst_exp (up_prog_type tau_type) (up_prog_prog tau_prog)
       (up_prog_exp tau_exp)) (up_prog_exp sigma) x = up_prog_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_exp id shift id (up_prog_type tau_type)
            (up_prog_prog tau_prog) (up_prog_exp tau_exp)
            (funcomp (up_prog_type tau_type) id)
            (funcomp (up_prog_prog tau_prog) shift)
            (funcomp (up_prog_exp tau_exp) id) (fun x => eq_refl)
            (fun x => eq_refl) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_exp tau_type tau_prog tau_exp id shift id
                  (funcomp (ren_type id) tau_type)
                  (funcomp (ren_prog id shift) tau_prog)
                  (funcomp (ren_exp id shift id) tau_exp) (fun x => eq_refl)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_exp id shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_exp_type (sigma : nat -> type) (tau_type : nat -> type)
  (theta : nat -> type)
  (Eq : forall x, funcomp (subst_type tau_type) sigma x = theta x) :
  forall x,
  funcomp (subst_type (up_exp_type tau_type)) (up_exp_type sigma) x =
  up_exp_type theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_type id (up_exp_type tau_type)
            (funcomp (up_exp_type tau_type) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_type tau_type id
                  (funcomp (ren_type id) tau_type) (fun x => eq_refl)
                  (sigma n))) (ap (ren_type id) (Eq n)))).
Qed.

Lemma up_subst_subst_exp_prog (sigma : nat -> prog) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (theta : nat -> prog)
  (Eq : forall x, funcomp (subst_prog tau_type tau_prog) sigma x = theta x) :
  forall x,
  funcomp (subst_prog (up_exp_type tau_type) (up_exp_prog tau_prog))
    (up_exp_prog sigma) x = up_exp_prog theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_prog id id (up_exp_type tau_type)
            (up_exp_prog tau_prog) (funcomp (up_exp_type tau_type) id)
            (funcomp (up_exp_prog tau_prog) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_prog tau_type tau_prog id id
                  (funcomp (ren_type id) tau_type)
                  (funcomp (ren_prog id id) tau_prog) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n))) (ap (ren_prog id id) (Eq n)))).
Qed.

Lemma up_subst_subst_exp_exp (sigma : nat -> exp) (tau_type : nat -> type)
  (tau_prog : nat -> prog) (tau_exp : nat -> exp) (theta : nat -> exp)
  (Eq : forall x,
        funcomp (subst_exp tau_type tau_prog tau_exp) sigma x = theta x) :
  forall x,
  funcomp
    (subst_exp (up_exp_type tau_type) (up_exp_prog tau_prog)
       (up_exp_exp tau_exp)) (up_exp_exp sigma) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_exp id id shift (up_exp_type tau_type)
                (up_exp_prog tau_prog) (up_exp_exp tau_exp)
                (funcomp (up_exp_type tau_type) id)
                (funcomp (up_exp_prog tau_prog) id)
                (funcomp (up_exp_exp tau_exp) shift) (fun x => eq_refl)
                (fun x => eq_refl) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_exp tau_type tau_prog tau_exp id id shift
                      (funcomp (ren_type id) tau_type)
                      (funcomp (ren_prog id id) tau_prog)
                      (funcomp (ren_exp id id shift) tau_exp)
                      (fun x => eq_refl) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_exp id id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_exp (sigma_type : nat -> type)
(sigma_prog : nat -> prog) (sigma_exp : nat -> exp) (tau_type : nat -> type)
(tau_prog : nat -> prog) (tau_exp : nat -> exp) (theta_type : nat -> type)
(theta_prog : nat -> prog) (theta_exp : nat -> exp)
(Eq_type : forall x,
           funcomp (subst_type tau_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (subst_prog tau_type tau_prog) sigma_prog x = theta_prog x)
(Eq_exp : forall x,
          funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp x =
          theta_exp x) (s : exp) {struct s} :
subst_exp tau_type tau_prog tau_exp
  (subst_exp sigma_type sigma_prog sigma_exp s) =
subst_exp theta_type theta_prog theta_exp s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_index sigma_type tau_type theta_type Eq_type s1)
        (compSubstSubst_spec (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp))
           (up_prog_type (up_exp_type tau_type))
           (up_prog_prog (up_exp_prog tau_prog))
           (up_prog_exp (up_exp_exp tau_exp))
           (up_prog_type (up_exp_type theta_type))
           (up_prog_prog (up_exp_prog theta_prog))
           (up_prog_exp (up_exp_exp theta_exp))
           (up_subst_subst_prog_type _ _ _
              (up_subst_subst_exp_type _ _ _ Eq_type))
           (up_subst_subst_prog_prog _ _ _ _
              (up_subst_subst_exp_prog _ _ _ _ Eq_prog))
           (up_subst_subst_prog_exp _ _ _ _ _
              (up_subst_subst_exp_exp _ _ _ _ _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (compSubstSubst_exp (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_exp sigma_exp)
           (up_type_type tau_type) (up_type_prog tau_prog)
           (up_type_exp tau_exp) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_type_exp theta_exp)
           (up_subst_subst_type_type _ _ _ Eq_type)
           (up_subst_subst_type_prog _ _ _ _ Eq_prog)
           (up_subst_subst_type_exp _ _ _ _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (compSubstSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
           tau_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s1)
  end
with compSubstSubst_spec (sigma_type : nat -> type)
(sigma_prog : nat -> prog) (sigma_exp : nat -> exp) (tau_type : nat -> type)
(tau_prog : nat -> prog) (tau_exp : nat -> exp) (theta_type : nat -> type)
(theta_prog : nat -> prog) (theta_exp : nat -> exp)
(Eq_type : forall x,
           funcomp (subst_type tau_type) sigma_type x = theta_type x)
(Eq_prog : forall x,
           funcomp (subst_prog tau_type tau_prog) sigma_prog x = theta_prog x)
(Eq_exp : forall x,
          funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp x =
          theta_exp x) (s : spec) {struct s} :
subst_spec tau_type tau_prog tau_exp
  (subst_spec sigma_type sigma_prog sigma_exp s) =
subst_spec theta_type theta_prog theta_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (compSubstSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
           tau_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s0)
        (compSubstSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
           tau_exp theta_type theta_prog theta_exp Eq_type Eq_prog Eq_exp s1)
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (compSubstSubst_spec sigma_type sigma_prog sigma_exp tau_type
           tau_prog tau_exp theta_type theta_prog theta_exp Eq_type Eq_prog
           Eq_exp s0)
        (compSubstSubst_spec sigma_type sigma_prog sigma_exp tau_type
           tau_prog tau_exp theta_type theta_prog theta_exp Eq_type Eq_prog
           Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (compSubstSubst_prog sigma_type sigma_prog tau_type tau_prog
           theta_type theta_prog Eq_type Eq_prog s0)
        (compSubstSubst_spec (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (up_prog_exp tau_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_subst_subst_prog_type _ _ _ Eq_type)
           (up_subst_subst_prog_prog _ _ _ _ Eq_prog)
           (up_subst_subst_prog_exp _ _ _ _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (compSubstSubst_spec (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_exp sigma_exp)
           (up_type_type tau_type) (up_type_prog tau_prog)
           (up_type_exp tau_exp) (up_type_type theta_type)
           (up_type_prog theta_prog) (up_type_exp theta_exp)
           (up_subst_subst_type_type _ _ _ Eq_type)
           (up_subst_subst_type_prog _ _ _ _ Eq_prog)
           (up_subst_subst_type_exp _ _ _ _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall
        (compSubstSubst_type sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_spec (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (up_prog_type tau_type) (up_prog_prog tau_prog)
           (up_prog_exp tau_exp) (up_prog_type theta_type)
           (up_prog_prog theta_prog) (up_prog_exp theta_exp)
           (up_subst_subst_prog_type _ _ _ Eq_type)
           (up_subst_subst_prog_prog _ _ _ _ Eq_prog)
           (up_subst_subst_prog_exp _ _ _ _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall
        (compSubstSubst_index sigma_type tau_type theta_type Eq_type s0)
        (compSubstSubst_spec (up_exp_type sigma_type)
           (up_exp_prog sigma_prog) (up_exp_exp sigma_exp)
           (up_exp_type tau_type) (up_exp_prog tau_prog) (up_exp_exp tau_exp)
           (up_exp_type theta_type) (up_exp_prog theta_prog)
           (up_exp_exp theta_exp) (up_subst_subst_exp_type _ _ _ Eq_type)
           (up_subst_subst_exp_prog _ _ _ _ Eq_prog)
           (up_subst_subst_exp_exp _ _ _ _ _ Eq_exp) s1)
  end.

Lemma renRen_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) (s : exp) :
  ren_exp zeta_type zeta_prog zeta_exp (ren_exp xi_type xi_prog xi_exp s) =
  ren_exp (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
    (funcomp zeta_exp xi_exp) s.
Proof.
exact (compRenRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_exp_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp)
       (ren_exp xi_type xi_prog xi_exp))
    (ren_exp (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
       (funcomp zeta_exp xi_exp)).
Proof.
exact (fun s =>
       compRenRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) (s : spec) :
  ren_spec zeta_type zeta_prog zeta_exp (ren_spec xi_type xi_prog xi_exp s) =
  ren_spec (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
    (funcomp zeta_exp xi_exp) s.
Proof.
exact (compRenRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp _
         _ _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_spec_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_spec zeta_type zeta_prog zeta_exp)
       (ren_spec xi_type xi_prog xi_exp))
    (ren_spec (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
       (funcomp zeta_exp xi_exp)).
Proof.
exact (fun s =>
       compRenRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp _
         _ _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) (s : exp) :
  subst_exp tau_type tau_prog tau_exp (ren_exp xi_type xi_prog xi_exp s) =
  subst_exp (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
    (funcomp tau_exp xi_exp) s.
Proof.
exact (compRenSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_exp tau_type tau_prog tau_exp)
       (ren_exp xi_type xi_prog xi_exp))
    (subst_exp (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
       (funcomp tau_exp xi_exp)).
Proof.
exact (fun s =>
       compRenSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) (s : spec) :
  subst_spec tau_type tau_prog tau_exp (ren_spec xi_type xi_prog xi_exp s) =
  subst_spec (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
    (funcomp tau_exp xi_exp) s.
Proof.
exact (compRenSubst_spec xi_type xi_prog xi_exp tau_type tau_prog tau_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_spec_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_spec tau_type tau_prog tau_exp)
       (ren_spec xi_type xi_prog xi_exp))
    (subst_spec (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
       (funcomp tau_exp xi_exp)).
Proof.
exact (fun s =>
       compRenSubst_spec xi_type xi_prog xi_exp tau_type tau_prog tau_exp _ _
         _ (fun n => eq_refl) (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) (s : exp) :
  ren_exp zeta_type zeta_prog zeta_exp
    (subst_exp sigma_type sigma_prog sigma_exp s) =
  subst_exp (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp) s.
Proof.
exact (compSubstRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
         zeta_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_exp_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (sigma_exp : nat -> exp)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp)
       (subst_exp sigma_type sigma_prog sigma_exp))
    (subst_exp (funcomp (ren_type zeta_type) sigma_type)
       (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
       (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
         zeta_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) (s : spec) :
  ren_spec zeta_type zeta_prog zeta_exp
    (subst_spec sigma_type sigma_prog sigma_exp s) =
  subst_spec (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp) s.
Proof.
exact (compSubstRen_spec sigma_type sigma_prog sigma_exp zeta_type zeta_prog
         zeta_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_spec_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (sigma_exp : nat -> exp)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_spec zeta_type zeta_prog zeta_exp)
       (subst_spec sigma_type sigma_prog sigma_exp))
    (subst_spec (funcomp (ren_type zeta_type) sigma_type)
       (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
       (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstRen_spec sigma_type sigma_prog sigma_exp zeta_type zeta_prog
         zeta_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) (s : exp) :
  subst_exp tau_type tau_prog tau_exp
    (subst_exp sigma_type sigma_prog sigma_exp s) =
  subst_exp (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog)
    (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
         tau_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (sigma_exp : nat -> exp)
  (tau_type : nat -> type) (tau_prog : nat -> prog) (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_exp tau_type tau_prog tau_exp)
       (subst_exp sigma_type sigma_prog sigma_exp))
    (subst_exp (funcomp (subst_type tau_type) sigma_type)
       (funcomp (subst_prog tau_type tau_prog) sigma_prog)
       (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
         tau_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) (s : spec) :
  subst_spec tau_type tau_prog tau_exp
    (subst_spec sigma_type sigma_prog sigma_exp s) =
  subst_spec (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog)
    (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_spec sigma_type sigma_prog sigma_exp tau_type tau_prog
         tau_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substSubst_spec_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (sigma_exp : nat -> exp)
  (tau_type : nat -> type) (tau_prog : nat -> prog) (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_spec tau_type tau_prog tau_exp)
       (subst_spec sigma_type sigma_prog sigma_exp))
    (subst_spec (funcomp (subst_type tau_type) sigma_type)
       (funcomp (subst_prog tau_type tau_prog) sigma_prog)
       (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_spec sigma_type sigma_prog sigma_exp tau_type tau_prog
         tau_exp _ _ _ (fun n => eq_refl) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_type_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (var_exp) xi x = sigma x) :
  forall x, funcomp (var_exp) (upRen_type_exp xi) x = up_type_exp sigma x.
Proof.
exact (fun n => ap (ren_exp shift id id) (Eq n)).
Qed.

Lemma rinstInst_up_prog_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (var_exp) xi x = sigma x) :
  forall x, funcomp (var_exp) (upRen_prog_exp xi) x = up_prog_exp sigma x.
Proof.
exact (fun n => ap (ren_exp id shift id) (Eq n)).
Qed.

Lemma rinstInst_up_exp_type (xi : nat -> nat) (sigma : nat -> type)
  (Eq : forall x, funcomp (var_type) xi x = sigma x) :
  forall x, funcomp (var_type) (upRen_exp_type xi) x = up_exp_type sigma x.
Proof.
exact (fun n => ap (ren_type id) (Eq n)).
Qed.

Lemma rinstInst_up_exp_prog (xi : nat -> nat) (sigma : nat -> prog)
  (Eq : forall x, funcomp (var_prog) xi x = sigma x) :
  forall x, funcomp (var_prog) (upRen_exp_prog xi) x = up_exp_prog sigma x.
Proof.
exact (fun n => ap (ren_prog id id) (Eq n)).
Qed.

Lemma rinstInst_up_exp_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (var_exp) xi x = sigma x) :
  forall x, funcomp (var_exp) (upRen_exp_exp xi) x = up_exp_exp sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp)
(Eq_type : forall x, funcomp (var_type) xi_type x = sigma_type x)
(Eq_prog : forall x, funcomp (var_prog) xi_prog x = sigma_prog x)
(Eq_exp : forall x, funcomp (var_exp) xi_exp x = sigma_exp x) (s : exp)
{struct s} :
ren_exp xi_type xi_prog xi_exp s =
subst_exp sigma_type sigma_prog sigma_exp s :=
  match s with
  | var_exp s0 => Eq_exp s0
  | cexp s0 s1 s2 =>
      congr_cexp (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_index xi_type sigma_type Eq_type s1)
        (rinst_inst_spec (upRen_prog_type (upRen_exp_type xi_type))
           (upRen_prog_prog (upRen_exp_prog xi_prog))
           (upRen_prog_exp (upRen_exp_exp xi_exp))
           (up_prog_type (up_exp_type sigma_type))
           (up_prog_prog (up_exp_prog sigma_prog))
           (up_prog_exp (up_exp_exp sigma_exp))
           (rinstInst_up_prog_type _ _ (rinstInst_up_exp_type _ _ Eq_type))
           (rinstInst_up_prog_prog _ _ (rinstInst_up_exp_prog _ _ Eq_prog))
           (rinstInst_up_prog_exp _ _ (rinstInst_up_exp_exp _ _ Eq_exp)) s2)
  | exabs s0 s1 =>
      congr_exabs (eq_refl s0)
        (rinst_inst_exp (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_exp sigma_exp)
           (rinstInst_up_type_type _ _ Eq_type)
           (rinstInst_up_type_prog _ _ Eq_prog)
           (rinstInst_up_type_exp _ _ Eq_exp) s1)
  | exapp s0 s1 =>
      congr_exapp
        (rinst_inst_exp xi_type xi_prog xi_exp sigma_type sigma_prog
           sigma_exp Eq_type Eq_prog Eq_exp s0)
        (rinst_inst_type xi_type sigma_type Eq_type s1)
  end
with rinst_inst_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
(xi_exp : nat -> nat) (sigma_type : nat -> type) (sigma_prog : nat -> prog)
(sigma_exp : nat -> exp)
(Eq_type : forall x, funcomp (var_type) xi_type x = sigma_type x)
(Eq_prog : forall x, funcomp (var_prog) xi_prog x = sigma_prog x)
(Eq_exp : forall x, funcomp (var_exp) xi_exp x = sigma_exp x) (s : spec)
{struct s} :
ren_spec xi_type xi_prog xi_exp s =
subst_spec sigma_type sigma_prog sigma_exp s :=
  match s with
  | spholds s0 s1 s2 =>
      congr_spholds
        (rinst_inst_exp xi_type xi_prog xi_exp sigma_type sigma_prog
           sigma_exp Eq_type Eq_prog Eq_exp s0)
        (rinst_inst_exp xi_type xi_prog xi_exp sigma_type sigma_prog
           sigma_exp Eq_type Eq_prog Eq_exp s1)
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s2)
  | spimplies s0 s1 =>
      congr_spimplies
        (rinst_inst_spec xi_type xi_prog xi_exp sigma_type sigma_prog
           sigma_exp Eq_type Eq_prog Eq_exp s0)
        (rinst_inst_spec xi_type xi_prog xi_exp sigma_type sigma_prog
           sigma_exp Eq_type Eq_prog Eq_exp s1)
  | after s0 s1 =>
      congr_after
        (rinst_inst_prog xi_type xi_prog sigma_type sigma_prog Eq_type
           Eq_prog s0)
        (rinst_inst_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (rinstInst_up_prog_type _ _ Eq_type)
           (rinstInst_up_prog_prog _ _ Eq_prog)
           (rinstInst_up_prog_exp _ _ Eq_exp) s1)
  | tyall s0 s1 =>
      congr_tyall (eq_refl s0)
        (rinst_inst_spec (upRen_type_type xi_type) (upRen_type_prog xi_prog)
           (upRen_type_exp xi_exp) (up_type_type sigma_type)
           (up_type_prog sigma_prog) (up_type_exp sigma_exp)
           (rinstInst_up_type_type _ _ Eq_type)
           (rinstInst_up_type_prog _ _ Eq_prog)
           (rinstInst_up_type_exp _ _ Eq_exp) s1)
  | tmall s0 s1 =>
      congr_tmall (rinst_inst_type xi_type sigma_type Eq_type s0)
        (rinst_inst_spec (upRen_prog_type xi_type) (upRen_prog_prog xi_prog)
           (upRen_prog_exp xi_exp) (up_prog_type sigma_type)
           (up_prog_prog sigma_prog) (up_prog_exp sigma_exp)
           (rinstInst_up_prog_type _ _ Eq_type)
           (rinstInst_up_prog_prog _ _ Eq_prog)
           (rinstInst_up_prog_exp _ _ Eq_exp) s1)
  | spall s0 s1 =>
      congr_spall (rinst_inst_index xi_type sigma_type Eq_type s0)
        (rinst_inst_spec (upRen_exp_type xi_type) (upRen_exp_prog xi_prog)
           (upRen_exp_exp xi_exp) (up_exp_type sigma_type)
           (up_exp_prog sigma_prog) (up_exp_exp sigma_exp)
           (rinstInst_up_exp_type _ _ Eq_type)
           (rinstInst_up_exp_prog _ _ Eq_prog)
           (rinstInst_up_exp_exp _ _ Eq_exp) s1)
  end.

Lemma rinstInst'_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (s : exp) :
  ren_exp xi_type xi_prog xi_exp s =
  subst_exp (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
    (funcomp (var_exp) xi_exp) s.
Proof.
exact (rinst_inst_exp xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_exp_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  pointwise_relation _ eq (ren_exp xi_type xi_prog xi_exp)
    (subst_exp (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
       (funcomp (var_exp) xi_exp)).
Proof.
exact (fun s =>
       rinst_inst_exp xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (s : spec) :
  ren_spec xi_type xi_prog xi_exp s =
  subst_spec (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
    (funcomp (var_exp) xi_exp) s.
Proof.
exact (rinst_inst_spec xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_spec_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  pointwise_relation _ eq (ren_spec xi_type xi_prog xi_exp)
    (subst_spec (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
       (funcomp (var_exp) xi_exp)).
Proof.
exact (fun s =>
       rinst_inst_spec xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_exp (s : exp) : subst_exp (var_type) (var_prog) (var_exp) s = s.
Proof.
exact (idSubst_exp (var_type) (var_prog) (var_exp) (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_exp_pointwise :
  pointwise_relation _ eq (subst_exp (var_type) (var_prog) (var_exp)) id.
Proof.
exact (fun s =>
       idSubst_exp (var_type) (var_prog) (var_exp) (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_spec (s : spec) :
  subst_spec (var_type) (var_prog) (var_exp) s = s.
Proof.
exact (idSubst_spec (var_type) (var_prog) (var_exp) (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma instId'_spec_pointwise :
  pointwise_relation _ eq (subst_spec (var_type) (var_prog) (var_exp)) id.
Proof.
exact (fun s =>
       idSubst_spec (var_type) (var_prog) (var_exp) (fun n => eq_refl)
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_exp (s : exp) : ren_exp id id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id id id s)).
Qed.

Lemma rinstId'_exp_pointwise : pointwise_relation _ eq (@ren_exp id id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id id id s)).
Qed.

Lemma rinstId'_spec (s : spec) : ren_spec id id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_spec s)
         (rinstInst'_spec id id id s)).
Qed.

Lemma rinstId'_spec_pointwise :
  pointwise_relation _ eq (@ren_spec id id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_spec s)
         (rinstInst'_spec id id id s)).
Qed.

Lemma varL'_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (x : nat) :
  subst_exp sigma_type sigma_prog sigma_exp (var_exp x) = sigma_exp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_exp_pointwise (sigma_type : nat -> type)
  (sigma_prog : nat -> prog) (sigma_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_exp sigma_type sigma_prog sigma_exp) (var_exp)) sigma_exp.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (x : nat) :
  ren_exp xi_type xi_prog xi_exp (var_exp x) = var_exp (xi_exp x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_exp_pointwise (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_exp xi_type xi_prog xi_exp) (var_exp))
    (funcomp (var_exp) xi_exp).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive term : Type :=
  | var_term : nat -> term
  | cterm : nat -> form -> term
with form : Type :=
  | implies : form -> form -> form
  | all : nat -> form -> form
  | holds : term -> term -> form.

Lemma congr_cterm {s0 : nat} {s1 : form} {t0 : nat} {t1 : form}
  (H0 : s0 = t0) (H1 : s1 = t1) : cterm s0 s1 = cterm t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => cterm x s1) H0))
         (ap (fun x => cterm t0 x) H1)).
Qed.

Lemma congr_implies {s0 : form} {s1 : form} {t0 : form} {t1 : form}
  (H0 : s0 = t0) (H1 : s1 = t1) : implies s0 s1 = implies t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => implies x s1) H0))
         (ap (fun x => implies t0 x) H1)).
Qed.

Lemma congr_all {s0 : nat} {s1 : form} {t0 : nat} {t1 : form} (H0 : s0 = t0)
  (H1 : s1 = t1) : all s0 s1 = all t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => all x s1) H0))
         (ap (fun x => all t0 x) H1)).
Qed.

Lemma congr_holds {s0 : term} {s1 : term} {t0 : term} {t1 : term}
  (H0 : s0 = t0) (H1 : s1 = t1) : holds s0 s1 = holds t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => holds x s1) H0))
         (ap (fun x => holds t0 x) H1)).
Qed.

Lemma upRen_term_term (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_term (xi_term : nat -> nat) (s : term) {struct s} : term :=
  match s with
  | var_term s0 => var_term (xi_term s0)
  | cterm s0 s1 => cterm s0 (ren_form (upRen_term_term xi_term) s1)
  end
with ren_form (xi_term : nat -> nat) (s : form) {struct s} : form :=
  match s with
  | implies s0 s1 => implies (ren_form xi_term s0) (ren_form xi_term s1)
  | all s0 s1 => all s0 (ren_form (upRen_term_term xi_term) s1)
  | holds s0 s1 => holds (ren_term xi_term s0) (ren_term xi_term s1)
  end.

Lemma up_term_term (sigma : nat -> term) : nat -> term.
Proof.
exact (scons (var_term var_zero) (funcomp (ren_term shift) sigma)).
Defined.

Fixpoint subst_term (sigma_term : nat -> term) (s : term) {struct s} : 
term :=
  match s with
  | var_term s0 => sigma_term s0
  | cterm s0 s1 => cterm s0 (subst_form (up_term_term sigma_term) s1)
  end
with subst_form (sigma_term : nat -> term) (s : form) {struct s} : form :=
  match s with
  | implies s0 s1 =>
      implies (subst_form sigma_term s0) (subst_form sigma_term s1)
  | all s0 s1 => all s0 (subst_form (up_term_term sigma_term) s1)
  | holds s0 s1 =>
      holds (subst_term sigma_term s0) (subst_term sigma_term s1)
  end.

Lemma upId_term_term (sigma : nat -> term)
  (Eq : forall x, sigma x = var_term x) :
  forall x, up_term_term sigma x = var_term x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_term (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var_term x) (s : term) {struct s} :
subst_term sigma_term s = s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  end
with idSubst_form (sigma_term : nat -> term)
(Eq_term : forall x, sigma_term x = var_term x) (s : form) {struct s} :
subst_form sigma_term s = s :=
  match s with
  | implies s0 s1 =>
      congr_implies (idSubst_form sigma_term Eq_term s0)
        (idSubst_form sigma_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (idSubst_form (up_term_term sigma_term) (upId_term_term _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds (idSubst_term sigma_term Eq_term s0)
        (idSubst_term sigma_term Eq_term s1)
  end.

Lemma upExtRen_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_term_term xi x = upRen_term_term zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : term) {struct s} :
ren_term xi_term s = ren_term zeta_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (extRen_form (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  end
with extRen_form (xi_term : nat -> nat) (zeta_term : nat -> nat)
(Eq_term : forall x, xi_term x = zeta_term x) (s : form) {struct s} :
ren_form xi_term s = ren_form zeta_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies (extRen_form xi_term zeta_term Eq_term s0)
        (extRen_form xi_term zeta_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (extRen_form (upRen_term_term xi_term) (upRen_term_term zeta_term)
           (upExtRen_term_term _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds (extRen_term xi_term zeta_term Eq_term s0)
        (extRen_term xi_term zeta_term Eq_term s1)
  end.

Lemma upExt_term_term (sigma : nat -> term) (tau : nat -> term)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_term_term sigma x = up_term_term tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_term (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : term) {struct s} :
subst_term sigma_term s = subst_term tau_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  end
with ext_form (sigma_term : nat -> term) (tau_term : nat -> term)
(Eq_term : forall x, sigma_term x = tau_term x) (s : form) {struct s} :
subst_form sigma_term s = subst_form tau_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies (ext_form sigma_term tau_term Eq_term s0)
        (ext_form sigma_term tau_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (ext_form (up_term_term sigma_term) (up_term_term tau_term)
           (upExt_term_term _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds (ext_term sigma_term tau_term Eq_term s0)
        (ext_term sigma_term tau_term Eq_term s1)
  end.

Lemma up_ren_ren_term_term (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_term_term zeta) (upRen_term_term xi) x =
  upRen_term_term rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : term)
{struct s} : ren_term zeta_term (ren_term xi_term s) = ren_term rho_term s :=
  match s with
  | var_term s0 => ap (var_term) (Eq_term s0)
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (compRenRen_form (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  end
with compRenRen_form (xi_term : nat -> nat) (zeta_term : nat -> nat)
(rho_term : nat -> nat)
(Eq_term : forall x, funcomp zeta_term xi_term x = rho_term x) (s : form)
{struct s} : ren_form zeta_term (ren_form xi_term s) = ren_form rho_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies (compRenRen_form xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_form xi_term zeta_term rho_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (compRenRen_form (upRen_term_term xi_term)
           (upRen_term_term zeta_term) (upRen_term_term rho_term)
           (up_ren_ren _ _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds (compRenRen_term xi_term zeta_term rho_term Eq_term s0)
        (compRenRen_term xi_term zeta_term rho_term Eq_term s1)
  end.

Lemma up_ren_subst_term_term (xi : nat -> nat) (tau : nat -> term)
  (theta : nat -> term) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_term_term tau) (upRen_term_term xi) x = up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : term)
{struct s} :
subst_term tau_term (ren_term xi_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (compRenSubst_form (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  end
with compRenSubst_form (xi_term : nat -> nat) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp tau_term xi_term x = theta_term x) (s : form)
{struct s} :
subst_form tau_term (ren_form xi_term s) = subst_form theta_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies
        (compRenSubst_form xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_form xi_term tau_term theta_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (compRenSubst_form (upRen_term_term xi_term) (up_term_term tau_term)
           (up_term_term theta_term) (up_ren_subst_term_term _ _ _ Eq_term)
           s1)
  | holds s0 s1 =>
      congr_holds (compRenSubst_term xi_term tau_term theta_term Eq_term s0)
        (compRenSubst_term xi_term tau_term theta_term Eq_term s1)
  end.

Lemma up_subst_ren_term_term (sigma : nat -> term) (zeta_term : nat -> nat)
  (theta : nat -> term)
  (Eq : forall x, funcomp (ren_term zeta_term) sigma x = theta x) :
  forall x,
  funcomp (ren_term (upRen_term_term zeta_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_term shift (upRen_term_term zeta_term)
                (funcomp shift zeta_term) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_term zeta_term shift (funcomp shift zeta_term)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_term (sigma_term : nat -> term)
(zeta_term : nat -> nat) (theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : term) {struct s} :
ren_term zeta_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (compSubstRen_form (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  end
with compSubstRen_form (sigma_term : nat -> term) (zeta_term : nat -> nat)
(theta_term : nat -> term)
(Eq_term : forall x, funcomp (ren_term zeta_term) sigma_term x = theta_term x)
(s : form) {struct s} :
ren_form zeta_term (subst_form sigma_term s) = subst_form theta_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies
        (compSubstRen_form sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_form sigma_term zeta_term theta_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (compSubstRen_form (up_term_term sigma_term)
           (upRen_term_term zeta_term) (up_term_term theta_term)
           (up_subst_ren_term_term _ _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s0)
        (compSubstRen_term sigma_term zeta_term theta_term Eq_term s1)
  end.

Lemma up_subst_subst_term_term (sigma : nat -> term) (tau_term : nat -> term)
  (theta : nat -> term)
  (Eq : forall x, funcomp (subst_term tau_term) sigma x = theta x) :
  forall x,
  funcomp (subst_term (up_term_term tau_term)) (up_term_term sigma) x =
  up_term_term theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_term shift (up_term_term tau_term)
                (funcomp (up_term_term tau_term) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_term tau_term shift
                      (funcomp (ren_term shift) tau_term) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_term shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_term (sigma_term : nat -> term)
(tau_term : nat -> term) (theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : term) {struct s} :
subst_term tau_term (subst_term sigma_term s) = subst_term theta_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  end
with compSubstSubst_form (sigma_term : nat -> term) (tau_term : nat -> term)
(theta_term : nat -> term)
(Eq_term : forall x,
           funcomp (subst_term tau_term) sigma_term x = theta_term x)
(s : form) {struct s} :
subst_form tau_term (subst_form sigma_term s) = subst_form theta_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_form sigma_term tau_term theta_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (compSubstSubst_form (up_term_term sigma_term)
           (up_term_term tau_term) (up_term_term theta_term)
           (up_subst_subst_term_term _ _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s0)
        (compSubstSubst_term sigma_term tau_term theta_term Eq_term s1)
  end.

Lemma renRen_term (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : term)
  :
  ren_term zeta_term (ren_term xi_term s) =
  ren_term (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_term_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_term zeta_term) (ren_term xi_term))
    (ren_term (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_term xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen_form (xi_term : nat -> nat) (zeta_term : nat -> nat) (s : form)
  :
  ren_form zeta_term (ren_form xi_term s) =
  ren_form (funcomp zeta_term xi_term) s.
Proof.
exact (compRenRen_form xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_form_pointwise (xi_term : nat -> nat) (zeta_term : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_form zeta_term) (ren_form xi_term))
    (ren_form (funcomp zeta_term xi_term)).
Proof.
exact (fun s => compRenRen_form xi_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (ren_term xi_term s) =
  subst_term (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_term_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_term tau_term) (ren_term xi_term))
    (subst_term (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_term xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_form (xi_term : nat -> nat) (tau_term : nat -> term)
  (s : form) :
  subst_form tau_term (ren_form xi_term s) =
  subst_form (funcomp tau_term xi_term) s.
Proof.
exact (compRenSubst_form xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_form_pointwise (xi_term : nat -> nat) (tau_term : nat -> term)
  :
  pointwise_relation _ eq (funcomp (subst_form tau_term) (ren_form xi_term))
    (subst_form (funcomp tau_term xi_term)).
Proof.
exact (fun s => compRenSubst_form xi_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : term) :
  ren_term zeta_term (subst_term sigma_term s) =
  subst_term (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_term_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_term zeta_term) (subst_term sigma_term))
    (subst_term (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_term sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_form (sigma_term : nat -> term) (zeta_term : nat -> nat)
  (s : form) :
  ren_form zeta_term (subst_form sigma_term s) =
  subst_form (funcomp (ren_term zeta_term) sigma_term) s.
Proof.
exact (compSubstRen_form sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substRen_form_pointwise (sigma_term : nat -> term)
  (zeta_term : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_form zeta_term) (subst_form sigma_term))
    (subst_form (funcomp (ren_term zeta_term) sigma_term)).
Proof.
exact (fun s => compSubstRen_form sigma_term zeta_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : term) :
  subst_term tau_term (subst_term sigma_term s) =
  subst_term (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_term_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_term tau_term) (subst_term sigma_term))
    (subst_term (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_term sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_form (sigma_term : nat -> term) (tau_term : nat -> term)
  (s : form) :
  subst_form tau_term (subst_form sigma_term s) =
  subst_form (funcomp (subst_term tau_term) sigma_term) s.
Proof.
exact (compSubstSubst_form sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_form_pointwise (sigma_term : nat -> term)
  (tau_term : nat -> term) :
  pointwise_relation _ eq
    (funcomp (subst_form tau_term) (subst_form sigma_term))
    (subst_form (funcomp (subst_term tau_term) sigma_term)).
Proof.
exact (fun s =>
       compSubstSubst_form sigma_term tau_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_term_term (xi : nat -> nat) (sigma : nat -> term)
  (Eq : forall x, funcomp (var_term) xi x = sigma x) :
  forall x, funcomp (var_term) (upRen_term_term xi) x = up_term_term sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_term shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_term (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : term)
{struct s} : ren_term xi_term s = subst_term sigma_term s :=
  match s with
  | var_term s0 => Eq_term s0
  | cterm s0 s1 =>
      congr_cterm (eq_refl s0)
        (rinst_inst_form (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  end
with rinst_inst_form (xi_term : nat -> nat) (sigma_term : nat -> term)
(Eq_term : forall x, funcomp (var_term) xi_term x = sigma_term x) (s : form)
{struct s} : ren_form xi_term s = subst_form sigma_term s :=
  match s with
  | implies s0 s1 =>
      congr_implies (rinst_inst_form xi_term sigma_term Eq_term s0)
        (rinst_inst_form xi_term sigma_term Eq_term s1)
  | all s0 s1 =>
      congr_all (eq_refl s0)
        (rinst_inst_form (upRen_term_term xi_term) (up_term_term sigma_term)
           (rinstInst_up_term_term _ _ Eq_term) s1)
  | holds s0 s1 =>
      congr_holds (rinst_inst_term xi_term sigma_term Eq_term s0)
        (rinst_inst_term xi_term sigma_term Eq_term s1)
  end.

Lemma rinstInst'_term (xi_term : nat -> nat) (s : term) :
  ren_term xi_term s = subst_term (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_term xi_term)
    (subst_term (funcomp (var_term) xi_term)).
Proof.
exact (fun s => rinst_inst_term xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_form (xi_term : nat -> nat) (s : form) :
  ren_form xi_term s = subst_form (funcomp (var_term) xi_term) s.
Proof.
exact (rinst_inst_form xi_term _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_form_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (ren_form xi_term)
    (subst_form (funcomp (var_term) xi_term)).
Proof.
exact (fun s => rinst_inst_form xi_term _ (fun n => eq_refl) s).
Qed.

Lemma instId'_term (s : term) : subst_term (var_term) s = s.
Proof.
exact (idSubst_term (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_term_pointwise :
  pointwise_relation _ eq (subst_term (var_term)) id.
Proof.
exact (fun s => idSubst_term (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_form (s : form) : subst_form (var_term) s = s.
Proof.
exact (idSubst_form (var_term) (fun n => eq_refl) s).
Qed.

Lemma instId'_form_pointwise :
  pointwise_relation _ eq (subst_form (var_term)) id.
Proof.
exact (fun s => idSubst_form (var_term) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_term (s : term) : ren_term id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_term_pointwise : pointwise_relation _ eq (@ren_term id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_term s) (rinstInst'_term id s)).
Qed.

Lemma rinstId'_form (s : form) : ren_form id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_form s) (rinstInst'_form id s)).
Qed.

Lemma rinstId'_form_pointwise : pointwise_relation _ eq (@ren_form id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_form s) (rinstInst'_form id s)).
Qed.

Lemma varL'_term (sigma_term : nat -> term) (x : nat) :
  subst_term sigma_term (var_term x) = sigma_term x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_term_pointwise (sigma_term : nat -> term) :
  pointwise_relation _ eq (funcomp (subst_term sigma_term) (var_term))
    sigma_term.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_term (xi_term : nat -> nat) (x : nat) :
  ren_term xi_term (var_term x) = var_term (xi_term x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_term_pointwise (xi_term : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_term xi_term) (var_term))
    (funcomp (var_term) xi_term).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_form X Y :=
    up_form : X -> Y.

Class Up_term X Y :=
    up_term : X -> Y.

Class Up_spec X Y :=
    up_spec : X -> Y.

Class Up_exp X Y :=
    up_exp : X -> Y.

Class Up_index X Y :=
    up_index : X -> Y.

Class Up_prog X Y :=
    up_prog : X -> Y.

Class Up_type X Y :=
    up_type : X -> Y.

#[global]Instance Subst_form : (Subst1 _ _ _) := @subst_form.

#[global]Instance Subst_term : (Subst1 _ _ _) := @subst_term.

#[global]Instance Up_term_term : (Up_term _ _) := @up_term_term.

#[global]Instance Ren_form : (Ren1 _ _ _) := @ren_form.

#[global]Instance Ren_term : (Ren1 _ _ _) := @ren_term.

#[global]Instance VarInstance_term : (Var _ _) := @var_term.

#[global]Instance Subst_spec : (Subst3 _ _ _ _ _) := @subst_spec.

#[global]Instance Subst_exp : (Subst3 _ _ _ _ _) := @subst_exp.

#[global]Instance Up_exp_exp : (Up_exp _ _) := @up_exp_exp.

#[global]Instance Up_exp_prog : (Up_prog _ _) := @up_exp_prog.

#[global]Instance Up_exp_type : (Up_type _ _) := @up_exp_type.

#[global]Instance Up_prog_exp : (Up_exp _ _) := @up_prog_exp.

#[global]Instance Up_type_exp : (Up_exp _ _) := @up_type_exp.

#[global]Instance Ren_spec : (Ren3 _ _ _ _ _) := @ren_spec.

#[global]Instance Ren_exp : (Ren3 _ _ _ _ _) := @ren_exp.

#[global]Instance VarInstance_exp : (Var _ _) := @var_exp.

#[global]Instance Subst_index : (Subst1 _ _ _) := @subst_index.

#[global]Instance Ren_index : (Ren1 _ _ _) := @ren_index.

#[global]Instance Subst_prog : (Subst2 _ _ _ _) := @subst_prog.

#[global]Instance Up_prog_prog : (Up_prog _ _) := @up_prog_prog.

#[global]Instance Up_prog_type : (Up_type _ _) := @up_prog_type.

#[global]Instance Up_type_prog : (Up_prog _ _) := @up_type_prog.

#[global]Instance Ren_prog : (Ren2 _ _ _ _) := @ren_prog.

#[global]Instance VarInstance_prog : (Var _ _) := @var_prog.

#[global]Instance Subst_type : (Subst1 _ _ _) := @subst_type.

#[global]Instance Up_type_type : (Up_type _ _) := @up_type_type.

#[global]Instance Ren_type : (Ren1 _ _ _) := @ren_type.

#[global]
Instance VarInstance_type : (Var _ _) := @var_type.

Notation "[ sigma_term ]" := (subst_form sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_term ]" := (subst_form sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__form" := up_form (only printing)  : subst_scope.

Notation "[ sigma_term ]" := (subst_term sigma_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_term ]" := (subst_term sigma_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__term" := up_term (only printing)  : subst_scope.

Notation "↑__term" := up_term_term (only printing)  : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_form xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_form xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "⟨ xi_term ⟩" := (ren_term xi_term)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_term ⟩" := (ren_term xi_term s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_term ( at level 1, only printing)  : subst_scope.

Notation "x '__term'" := (@ids _ _ VarInstance_term x)
( at level 5, format "x __term", only printing)  : subst_scope.

Notation "x '__term'" := (var_term x) ( at level 5, format "x __term")  :
subst_scope.

Notation "[ sigma_type ; sigma_prog ; sigma_exp ]" :=
(subst_spec sigma_type sigma_prog sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_type ; sigma_prog ; sigma_exp ]" :=
(subst_spec sigma_type sigma_prog sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__spec" := up_spec (only printing)  : subst_scope.

Notation "[ sigma_type ; sigma_prog ; sigma_exp ]" :=
(subst_exp sigma_type sigma_prog sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_type ; sigma_prog ; sigma_exp ]" :=
(subst_exp sigma_type sigma_prog sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__exp" := up_exp (only printing)  : subst_scope.

Notation "↑__exp" := up_exp_exp (only printing)  : subst_scope.

Notation "↑__prog" := up_exp_prog (only printing)  : subst_scope.

Notation "↑__type" := up_exp_type (only printing)  : subst_scope.

Notation "↑__exp" := up_prog_exp (only printing)  : subst_scope.

Notation "↑__exp" := up_type_exp (only printing)  : subst_scope.

Notation "⟨ xi_type ; xi_prog ; xi_exp ⟩" :=
(ren_spec xi_type xi_prog xi_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_type ; xi_prog ; xi_exp ⟩" :=
(ren_spec xi_type xi_prog xi_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "⟨ xi_type ; xi_prog ; xi_exp ⟩" := (ren_exp xi_type xi_prog xi_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_type ; xi_prog ; xi_exp ⟩" :=
(ren_exp xi_type xi_prog xi_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_exp ( at level 1, only printing)  : subst_scope.

Notation "x '__exp'" := (@ids _ _ VarInstance_exp x)
( at level 5, format "x __exp", only printing)  : subst_scope.

Notation "x '__exp'" := (var_exp x) ( at level 5, format "x __exp")  :
subst_scope.

Notation "[ sigma_type ]" := (subst_index sigma_type)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_type ]" := (subst_index sigma_type s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__index" := up_index (only printing)  : subst_scope.

Notation "⟨ xi_type ⟩" := (ren_index xi_type)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_type ⟩" := (ren_index xi_type s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "[ sigma_type ; sigma_prog ]" := (subst_prog sigma_type sigma_prog)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_type ; sigma_prog ]" :=
(subst_prog sigma_type sigma_prog s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__prog" := up_prog (only printing)  : subst_scope.

Notation "↑__prog" := up_prog_prog (only printing)  : subst_scope.

Notation "↑__type" := up_prog_type (only printing)  : subst_scope.

Notation "↑__prog" := up_type_prog (only printing)  : subst_scope.

Notation "⟨ xi_type ; xi_prog ⟩" := (ren_prog xi_type xi_prog)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_type ; xi_prog ⟩" := (ren_prog xi_type xi_prog s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_prog ( at level 1, only printing)  : subst_scope.

Notation "x '__prog'" := (@ids _ _ VarInstance_prog x)
( at level 5, format "x __prog", only printing)  : subst_scope.

Notation "x '__prog'" := (var_prog x) ( at level 5, format "x __prog")  :
subst_scope.

Notation "[ sigma_type ]" := (subst_type sigma_type)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_type ]" := (subst_type sigma_type s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__type" := up_type (only printing)  : subst_scope.

Notation "↑__type" := up_type_type (only printing)  : subst_scope.

Notation "⟨ xi_type ⟩" := (ren_type xi_type)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_type ⟩" := (ren_type xi_type s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := var_type ( at level 1, only printing)  : subst_scope.

Notation "x '__type'" := (@ids _ _ VarInstance_type x)
( at level 5, format "x __type", only printing)  : subst_scope.

Notation "x '__type'" := (var_type x) ( at level 5, format "x __type")  :
subst_scope.

#[global]
Instance subst_form_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_form)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_form f_term s = subst_form g_term t')
         (ext_form f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_form_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_form)).
Proof.
exact (fun f_term g_term Eq_term s => ext_form f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => subst_term f_term s = subst_term g_term t')
         (ext_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance subst_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_term)).
Proof.
exact (fun f_term g_term Eq_term s => ext_term f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_form_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_form)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_form f_term s = ren_form g_term t')
         (extRen_form f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_form_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_form)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_form f_term g_term Eq_term s).
Qed.

#[global]
Instance ren_term_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s t Eq_st =>
       eq_ind s (fun t' => ren_term f_term s = ren_term g_term t')
         (extRen_term f_term g_term Eq_term s) t Eq_st).
Qed.

#[global]
Instance ren_term_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_term)).
Proof.
exact (fun f_term g_term Eq_term s => extRen_term f_term g_term Eq_term s).
Qed.

#[global]
Instance subst_spec_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (respectful eq eq))))
    (@subst_spec)).
Proof.
exact (fun
         f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s t
          Eq_st =>
       eq_ind s
         (fun t' =>
          subst_spec f_type f_prog f_exp s =
          subst_spec g_type g_prog g_exp t')
         (ext_spec f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
            Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_spec_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))))
    (@subst_spec)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s
       =>
       ext_spec f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
         Eq_exp s).
Qed.

#[global]
Instance subst_exp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (respectful eq eq))))
    (@subst_exp)).
Proof.
exact (fun
         f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s t
          Eq_st =>
       eq_ind s
         (fun t' =>
          subst_exp f_type f_prog f_exp s = subst_exp g_type g_prog g_exp t')
         (ext_exp f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
            Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_exp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))))
    (@subst_exp)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s
       =>
       ext_exp f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog Eq_exp
         s).
Qed.

#[global]
Instance ren_spec_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (respectful eq eq))))
    (@ren_spec)).
Proof.
exact (fun
         f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s t
          Eq_st =>
       eq_ind s
         (fun t' =>
          ren_spec f_type f_prog f_exp s = ren_spec g_type g_prog g_exp t')
         (extRen_spec f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
            Eq_exp s) t Eq_st).
Qed.

#[global]
Instance ren_spec_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))))
    (@ren_spec)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s
       =>
       extRen_spec f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
         Eq_exp s).
Qed.

#[global]
Instance ren_exp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (respectful eq eq))))
    (@ren_exp)).
Proof.
exact (fun
         f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s t
          Eq_st =>
       eq_ind s
         (fun t' =>
          ren_exp f_type f_prog f_exp s = ren_exp g_type g_prog g_exp t')
         (extRen_exp f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
            Eq_exp s) t Eq_st).
Qed.

#[global]
Instance ren_exp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq)
          (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))))
    (@ren_exp)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog f_exp g_exp Eq_exp s
       =>
       extRen_exp f_type f_prog f_exp g_type g_prog g_exp Eq_type Eq_prog
         Eq_exp s).
Qed.

#[global]
Instance subst_index_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_index)).
Proof.
exact (fun f_type g_type Eq_type s t Eq_st =>
       eq_ind s (fun t' => subst_index f_type s = subst_index g_type t')
         (ext_index f_type g_type Eq_type s) t Eq_st).
Qed.

#[global]
Instance subst_index_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_index)).
Proof.
exact (fun f_type g_type Eq_type s => ext_index f_type g_type Eq_type s).
Qed.

#[global]
Instance ren_index_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_index)).
Proof.
exact (fun f_type g_type Eq_type s t Eq_st =>
       eq_ind s (fun t' => ren_index f_type s = ren_index g_type t')
         (extRen_index f_type g_type Eq_type s) t Eq_st).
Qed.

#[global]
Instance ren_index_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_index)).
Proof.
exact (fun f_type g_type Eq_type s => extRen_index f_type g_type Eq_type s).
Qed.

#[global]
Instance subst_prog_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_prog)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog s t Eq_st =>
       eq_ind s
         (fun t' => subst_prog f_type f_prog s = subst_prog g_type g_prog t')
         (ext_prog f_type f_prog g_type g_prog Eq_type Eq_prog s) t Eq_st).
Qed.

#[global]
Instance subst_prog_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_prog)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog s =>
       ext_prog f_type f_prog g_type g_prog Eq_type Eq_prog s).
Qed.

#[global]
Instance ren_prog_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_prog)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog s t Eq_st =>
       eq_ind s
         (fun t' => ren_prog f_type f_prog s = ren_prog g_type g_prog t')
         (extRen_prog f_type f_prog g_type g_prog Eq_type Eq_prog s) t Eq_st).
Qed.

#[global]
Instance ren_prog_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_prog)).
Proof.
exact (fun f_type g_type Eq_type f_prog g_prog Eq_prog s =>
       extRen_prog f_type f_prog g_type g_prog Eq_type Eq_prog s).
Qed.

#[global]
Instance subst_type_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_type)).
Proof.
exact (fun f_type g_type Eq_type s t Eq_st =>
       eq_ind s (fun t' => subst_type f_type s = subst_type g_type t')
         (ext_type f_type g_type Eq_type s) t Eq_st).
Qed.

#[global]
Instance subst_type_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_type)).
Proof.
exact (fun f_type g_type Eq_type s => ext_type f_type g_type Eq_type s).
Qed.

#[global]
Instance ren_type_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_type)).
Proof.
exact (fun f_type g_type Eq_type s t Eq_st =>
       eq_ind s (fun t' => ren_type f_type s = ren_type g_type t')
         (extRen_type f_type g_type Eq_type s) t Eq_st).
Qed.

#[global]
Instance ren_type_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_type)).
Proof.
exact (fun f_type g_type Eq_type s => extRen_type f_type g_type Eq_type s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_type, Var, ids, Ren_type, Ren1, ren1,
                      Up_type_type, Up_type, up_type, Subst_type, Subst1,
                      subst1, VarInstance_prog, Var, ids, Ren_prog, Ren2,
                      ren2, Up_type_prog, Up_prog, up_prog, Up_prog_type,
                      Up_type, up_type, Up_prog_prog, Up_prog, up_prog,
                      Subst_prog, Subst2, subst2, Ren_index, Ren1, ren1,
                      Subst_index, Subst1, subst1, VarInstance_exp, Var, ids,
                      Ren_exp, Ren3, ren3, Ren_spec, Ren3, ren3, Up_type_exp,
                      Up_exp, up_exp, Up_prog_exp, Up_exp, up_exp,
                      Up_exp_type, Up_type, up_type, Up_exp_prog, Up_prog,
                      up_prog, Up_exp_exp, Up_exp, up_exp, Subst_exp, Subst3,
                      subst3, Subst_spec, Subst3, subst3, VarInstance_term,
                      Var, ids, Ren_term, Ren1, ren1, Ren_form, Ren1, ren1,
                      Up_term_term, Up_term, up_term, Subst_term, Subst1,
                      subst1, Subst_form, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_type, Var, ids,
                                            Ren_type, Ren1, ren1,
                                            Up_type_type, Up_type, up_type,
                                            Subst_type, Subst1, subst1,
                                            VarInstance_prog, Var, ids,
                                            Ren_prog, Ren2, ren2,
                                            Up_type_prog, Up_prog, up_prog,
                                            Up_prog_type, Up_type, up_type,
                                            Up_prog_prog, Up_prog, up_prog,
                                            Subst_prog, Subst2, subst2,
                                            Ren_index, Ren1, ren1,
                                            Subst_index, Subst1, subst1,
                                            VarInstance_exp, Var, ids,
                                            Ren_exp, Ren3, ren3, Ren_spec,
                                            Ren3, ren3, Up_type_exp, Up_exp,
                                            up_exp, Up_prog_exp, Up_exp,
                                            up_exp, Up_exp_type, Up_type,
                                            up_type, Up_exp_prog, Up_prog,
                                            up_prog, Up_exp_exp, Up_exp,
                                            up_exp, Subst_exp, Subst3,
                                            subst3, Subst_spec, Subst3,
                                            subst3, VarInstance_term, Var,
                                            ids, Ren_term, Ren1, ren1,
                                            Ren_form, Ren1, ren1,
                                            Up_term_term, Up_term, up_term,
                                            Subst_term, Subst1, subst1,
                                            Subst_form, Subst1, subst1 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_form_pointwise
                 | progress setoid_rewrite substSubst_form
                 | progress setoid_rewrite substSubst_term_pointwise
                 | progress setoid_rewrite substSubst_term
                 | progress setoid_rewrite substRen_form_pointwise
                 | progress setoid_rewrite substRen_form
                 | progress setoid_rewrite substRen_term_pointwise
                 | progress setoid_rewrite substRen_term
                 | progress setoid_rewrite renSubst_form_pointwise
                 | progress setoid_rewrite renSubst_form
                 | progress setoid_rewrite renSubst_term_pointwise
                 | progress setoid_rewrite renSubst_term
                 | progress setoid_rewrite renRen'_form_pointwise
                 | progress setoid_rewrite renRen_form
                 | progress setoid_rewrite renRen'_term_pointwise
                 | progress setoid_rewrite renRen_term
                 | progress setoid_rewrite substSubst_spec_pointwise
                 | progress setoid_rewrite substSubst_spec
                 | progress setoid_rewrite substSubst_exp_pointwise
                 | progress setoid_rewrite substSubst_exp
                 | progress setoid_rewrite substRen_spec_pointwise
                 | progress setoid_rewrite substRen_spec
                 | progress setoid_rewrite substRen_exp_pointwise
                 | progress setoid_rewrite substRen_exp
                 | progress setoid_rewrite renSubst_spec_pointwise
                 | progress setoid_rewrite renSubst_spec
                 | progress setoid_rewrite renSubst_exp_pointwise
                 | progress setoid_rewrite renSubst_exp
                 | progress setoid_rewrite renRen'_spec_pointwise
                 | progress setoid_rewrite renRen_spec
                 | progress setoid_rewrite renRen'_exp_pointwise
                 | progress setoid_rewrite renRen_exp
                 | progress setoid_rewrite substSubst_index_pointwise
                 | progress setoid_rewrite substSubst_index
                 | progress setoid_rewrite substRen_index_pointwise
                 | progress setoid_rewrite substRen_index
                 | progress setoid_rewrite renSubst_index_pointwise
                 | progress setoid_rewrite renSubst_index
                 | progress setoid_rewrite renRen'_index_pointwise
                 | progress setoid_rewrite renRen_index
                 | progress setoid_rewrite substSubst_prog_pointwise
                 | progress setoid_rewrite substSubst_prog
                 | progress setoid_rewrite substRen_prog_pointwise
                 | progress setoid_rewrite substRen_prog
                 | progress setoid_rewrite renSubst_prog_pointwise
                 | progress setoid_rewrite renSubst_prog
                 | progress setoid_rewrite renRen'_prog_pointwise
                 | progress setoid_rewrite renRen_prog
                 | progress setoid_rewrite substSubst_type_pointwise
                 | progress setoid_rewrite substSubst_type
                 | progress setoid_rewrite substRen_type_pointwise
                 | progress setoid_rewrite substRen_type
                 | progress setoid_rewrite renSubst_type_pointwise
                 | progress setoid_rewrite renSubst_type
                 | progress setoid_rewrite renRen'_type_pointwise
                 | progress setoid_rewrite renRen_type
                 | progress setoid_rewrite varLRen'_term_pointwise
                 | progress setoid_rewrite varLRen'_term
                 | progress setoid_rewrite varL'_term_pointwise
                 | progress setoid_rewrite varL'_term
                 | progress setoid_rewrite rinstId'_form_pointwise
                 | progress setoid_rewrite rinstId'_form
                 | progress setoid_rewrite rinstId'_term_pointwise
                 | progress setoid_rewrite rinstId'_term
                 | progress setoid_rewrite instId'_form_pointwise
                 | progress setoid_rewrite instId'_form
                 | progress setoid_rewrite instId'_term_pointwise
                 | progress setoid_rewrite instId'_term
                 | progress setoid_rewrite varLRen'_exp_pointwise
                 | progress setoid_rewrite varLRen'_exp
                 | progress setoid_rewrite varL'_exp_pointwise
                 | progress setoid_rewrite varL'_exp
                 | progress setoid_rewrite rinstId'_spec_pointwise
                 | progress setoid_rewrite rinstId'_spec
                 | progress setoid_rewrite rinstId'_exp_pointwise
                 | progress setoid_rewrite rinstId'_exp
                 | progress setoid_rewrite instId'_spec_pointwise
                 | progress setoid_rewrite instId'_spec
                 | progress setoid_rewrite instId'_exp_pointwise
                 | progress setoid_rewrite instId'_exp
                 | progress setoid_rewrite rinstId'_index_pointwise
                 | progress setoid_rewrite rinstId'_index
                 | progress setoid_rewrite instId'_index_pointwise
                 | progress setoid_rewrite instId'_index
                 | progress setoid_rewrite varLRen'_prog_pointwise
                 | progress setoid_rewrite varLRen'_prog
                 | progress setoid_rewrite varL'_prog_pointwise
                 | progress setoid_rewrite varL'_prog
                 | progress setoid_rewrite rinstId'_prog_pointwise
                 | progress setoid_rewrite rinstId'_prog
                 | progress setoid_rewrite instId'_prog_pointwise
                 | progress setoid_rewrite instId'_prog
                 | progress setoid_rewrite varLRen'_type_pointwise
                 | progress setoid_rewrite varLRen'_type
                 | progress setoid_rewrite varL'_type_pointwise
                 | progress setoid_rewrite varL'_type
                 | progress setoid_rewrite rinstId'_type_pointwise
                 | progress setoid_rewrite rinstId'_type
                 | progress setoid_rewrite instId'_type_pointwise
                 | progress setoid_rewrite instId'_type
                 | progress
                    unfold up_term_term, upRen_term_term, up_exp_exp,
                     up_exp_prog, up_exp_type, up_prog_exp, up_type_exp,
                     upRen_exp_exp, upRen_exp_prog, upRen_exp_type,
                     upRen_prog_exp, upRen_type_exp, up_prog_prog,
                     up_prog_type, up_type_prog, upRen_prog_prog,
                     upRen_prog_type, upRen_type_prog, up_type_type,
                     upRen_type_type, up_ren
                 | progress
                    cbn[subst_form subst_term ren_form ren_term subst_spec
                       subst_exp ren_spec ren_exp subst_index ren_index
                       subst_prog ren_prog subst_type ren_type]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_type, Var, ids, Ren_type, Ren1, ren1,
                  Up_type_type, Up_type, up_type, Subst_type, Subst1, subst1,
                  VarInstance_prog, Var, ids, Ren_prog, Ren2, ren2,
                  Up_type_prog, Up_prog, up_prog, Up_prog_type, Up_type,
                  up_type, Up_prog_prog, Up_prog, up_prog, Subst_prog,
                  Subst2, subst2, Ren_index, Ren1, ren1, Subst_index, Subst1,
                  subst1, VarInstance_exp, Var, ids, Ren_exp, Ren3, ren3,
                  Ren_spec, Ren3, ren3, Up_type_exp, Up_exp, up_exp,
                  Up_prog_exp, Up_exp, up_exp, Up_exp_type, Up_type, up_type,
                  Up_exp_prog, Up_prog, up_prog, Up_exp_exp, Up_exp, up_exp,
                  Subst_exp, Subst3, subst3, Subst_spec, Subst3, subst3,
                  VarInstance_term, Var, ids, Ren_term, Ren1, ren1, Ren_form,
                  Ren1, ren1, Up_term_term, Up_term, up_term, Subst_term,
                  Subst1, subst1, Subst_form, Subst1, subst1 in *; asimpl';
                minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_form_pointwise;
                  try setoid_rewrite rinstInst'_form;
                  try setoid_rewrite rinstInst'_term_pointwise;
                  try setoid_rewrite rinstInst'_term;
                  try setoid_rewrite rinstInst'_spec_pointwise;
                  try setoid_rewrite rinstInst'_spec;
                  try setoid_rewrite rinstInst'_exp_pointwise;
                  try setoid_rewrite rinstInst'_exp;
                  try setoid_rewrite rinstInst'_index_pointwise;
                  try setoid_rewrite rinstInst'_index;
                  try setoid_rewrite rinstInst'_prog_pointwise;
                  try setoid_rewrite rinstInst'_prog;
                  try setoid_rewrite rinstInst'_type_pointwise;
                  try setoid_rewrite rinstInst'_type.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_form_pointwise;
                  try setoid_rewrite_left rinstInst'_form;
                  try setoid_rewrite_left rinstInst'_term_pointwise;
                  try setoid_rewrite_left rinstInst'_term;
                  try setoid_rewrite_left rinstInst'_spec_pointwise;
                  try setoid_rewrite_left rinstInst'_spec;
                  try setoid_rewrite_left rinstInst'_exp_pointwise;
                  try setoid_rewrite_left rinstInst'_exp;
                  try setoid_rewrite_left rinstInst'_index_pointwise;
                  try setoid_rewrite_left rinstInst'_index;
                  try setoid_rewrite_left rinstInst'_prog_pointwise;
                  try setoid_rewrite_left rinstInst'_prog;
                  try setoid_rewrite_left rinstInst'_type_pointwise;
                  try setoid_rewrite_left rinstInst'_type.

End Core.

Module Fext.

Import
Core.

Lemma renRen'_type (xi_type : nat -> nat) (zeta_type : nat -> nat) :
  funcomp (ren_type zeta_type) (ren_type xi_type) =
  ren_type (funcomp zeta_type xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_type xi_type zeta_type n)).
Qed.

Lemma renSubst'_type (xi_type : nat -> nat) (tau_type : nat -> type) :
  funcomp (subst_type tau_type) (ren_type xi_type) =
  subst_type (funcomp tau_type xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_type xi_type tau_type n)).
Qed.

Lemma substRen'_type (sigma_type : nat -> type) (zeta_type : nat -> nat) :
  funcomp (ren_type zeta_type) (subst_type sigma_type) =
  subst_type (funcomp (ren_type zeta_type) sigma_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_type sigma_type zeta_type n)).
Qed.

Lemma substSubst'_type (sigma_type : nat -> type) (tau_type : nat -> type) :
  funcomp (subst_type tau_type) (subst_type sigma_type) =
  subst_type (funcomp (subst_type tau_type) sigma_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_type sigma_type tau_type n)).
Qed.

Lemma rinstInst_type (xi_type : nat -> nat) :
  ren_type xi_type = subst_type (funcomp (var_type) xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_type xi_type _ (fun n => eq_refl) x)).
Qed.

Lemma instId_type : subst_type (var_type) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_type (var_type) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_type : @ren_type id = id.
Proof.
exact (eq_trans (rinstInst_type (id _)) instId_type).
Qed.

Lemma varL_type (sigma_type : nat -> type) :
  funcomp (subst_type sigma_type) (var_type) = sigma_type.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_type (xi_type : nat -> nat) :
  funcomp (ren_type xi_type) (var_type) = funcomp (var_type) xi_type.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) :
  funcomp (ren_prog zeta_type zeta_prog) (ren_prog xi_type xi_prog) =
  ren_prog (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_prog xi_type xi_prog zeta_type zeta_prog n)).
Qed.

Lemma renSubst'_prog (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (tau_type : nat -> type) (tau_prog : nat -> prog) :
  funcomp (subst_prog tau_type tau_prog) (ren_prog xi_type xi_prog) =
  subst_prog (funcomp tau_type xi_type) (funcomp tau_prog xi_prog).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_prog xi_type xi_prog tau_type tau_prog n)).
Qed.

Lemma substRen'_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (zeta_type : nat -> nat) (zeta_prog : nat -> nat) :
  funcomp (ren_prog zeta_type zeta_prog) (subst_prog sigma_type sigma_prog) =
  subst_prog (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_prog sigma_type sigma_prog zeta_type zeta_prog n)).
Qed.

Lemma substSubst'_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (tau_type : nat -> type) (tau_prog : nat -> prog) :
  funcomp (subst_prog tau_type tau_prog) (subst_prog sigma_type sigma_prog) =
  subst_prog (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_prog sigma_type sigma_prog tau_type tau_prog n)).
Qed.

Lemma rinstInst_prog (xi_type : nat -> nat) (xi_prog : nat -> nat) :
  ren_prog xi_type xi_prog =
  subst_prog (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_prog xi_type xi_prog _ _ (fun n => eq_refl)
            (fun n => eq_refl) x)).
Qed.

Lemma instId_prog : subst_prog (var_type) (var_prog) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_prog (var_type) (var_prog) (fun n => eq_refl)
            (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_prog : @ren_prog id id = id.
Proof.
exact (eq_trans (rinstInst_prog (id _) (id _)) instId_prog).
Qed.

Lemma varL_prog (sigma_type : nat -> type) (sigma_prog : nat -> prog) :
  funcomp (subst_prog sigma_type sigma_prog) (var_prog) = sigma_prog.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_prog (xi_type : nat -> nat) (xi_prog : nat -> nat) :
  funcomp (ren_prog xi_type xi_prog) (var_prog) = funcomp (var_prog) xi_prog.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_index (xi_type : nat -> nat) (zeta_type : nat -> nat) :
  funcomp (ren_index zeta_type) (ren_index xi_type) =
  ren_index (funcomp zeta_type xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_index xi_type zeta_type n)).
Qed.

Lemma renSubst'_index (xi_type : nat -> nat) (tau_type : nat -> type) :
  funcomp (subst_index tau_type) (ren_index xi_type) =
  subst_index (funcomp tau_type xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_index xi_type tau_type n)).
Qed.

Lemma substRen'_index (sigma_type : nat -> type) (zeta_type : nat -> nat) :
  funcomp (ren_index zeta_type) (subst_index sigma_type) =
  subst_index (funcomp (ren_type zeta_type) sigma_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_index sigma_type zeta_type n)).
Qed.

Lemma substSubst'_index (sigma_type : nat -> type) (tau_type : nat -> type) :
  funcomp (subst_index tau_type) (subst_index sigma_type) =
  subst_index (funcomp (subst_type tau_type) sigma_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_index sigma_type tau_type n)).
Qed.

Lemma rinstInst_index (xi_type : nat -> nat) :
  ren_index xi_type = subst_index (funcomp (var_type) xi_type).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_index xi_type _ (fun n => eq_refl) x)).
Qed.

Lemma instId_index : subst_index (var_type) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_index (var_type) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_index : @ren_index id = id.
Proof.
exact (eq_trans (rinstInst_index (id _)) instId_index).
Qed.

Lemma renRen'_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  funcomp (ren_exp zeta_type zeta_prog zeta_exp)
    (ren_exp xi_type xi_prog xi_exp) =
  ren_exp (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
    (funcomp zeta_exp xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          renRen_exp xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp n)).
Qed.

Lemma renRen'_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  funcomp (ren_spec zeta_type zeta_prog zeta_exp)
    (ren_spec xi_type xi_prog xi_exp) =
  ren_spec (funcomp zeta_type xi_type) (funcomp zeta_prog xi_prog)
    (funcomp zeta_exp xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          renRen_spec xi_type xi_prog xi_exp zeta_type zeta_prog zeta_exp n)).
Qed.

Lemma renSubst'_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  funcomp (subst_exp tau_type tau_prog tau_exp)
    (ren_exp xi_type xi_prog xi_exp) =
  subst_exp (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
    (funcomp tau_exp xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          renSubst_exp xi_type xi_prog xi_exp tau_type tau_prog tau_exp n)).
Qed.

Lemma renSubst'_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  funcomp (subst_spec tau_type tau_prog tau_exp)
    (ren_spec xi_type xi_prog xi_exp) =
  subst_spec (funcomp tau_type xi_type) (funcomp tau_prog xi_prog)
    (funcomp tau_exp xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          renSubst_spec xi_type xi_prog xi_exp tau_type tau_prog tau_exp n)).
Qed.

Lemma substRen'_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  funcomp (ren_exp zeta_type zeta_prog zeta_exp)
    (subst_exp sigma_type sigma_prog sigma_exp) =
  subst_exp (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          substRen_exp sigma_type sigma_prog sigma_exp zeta_type zeta_prog
            zeta_exp n)).
Qed.

Lemma substRen'_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (zeta_type : nat -> nat) (zeta_prog : nat -> nat)
  (zeta_exp : nat -> nat) :
  funcomp (ren_spec zeta_type zeta_prog zeta_exp)
    (subst_spec sigma_type sigma_prog sigma_exp) =
  subst_spec (funcomp (ren_type zeta_type) sigma_type)
    (funcomp (ren_prog zeta_type zeta_prog) sigma_prog)
    (funcomp (ren_exp zeta_type zeta_prog zeta_exp) sigma_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          substRen_spec sigma_type sigma_prog sigma_exp zeta_type zeta_prog
            zeta_exp n)).
Qed.

Lemma substSubst'_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  funcomp (subst_exp tau_type tau_prog tau_exp)
    (subst_exp sigma_type sigma_prog sigma_exp) =
  subst_exp (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog)
    (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          substSubst_exp sigma_type sigma_prog sigma_exp tau_type tau_prog
            tau_exp n)).
Qed.

Lemma substSubst'_spec (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) (tau_type : nat -> type) (tau_prog : nat -> prog)
  (tau_exp : nat -> exp) :
  funcomp (subst_spec tau_type tau_prog tau_exp)
    (subst_spec sigma_type sigma_prog sigma_exp) =
  subst_spec (funcomp (subst_type tau_type) sigma_type)
    (funcomp (subst_prog tau_type tau_prog) sigma_prog)
    (funcomp (subst_exp tau_type tau_prog tau_exp) sigma_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n =>
          substSubst_spec sigma_type sigma_prog sigma_exp tau_type tau_prog
            tau_exp n)).
Qed.

Lemma rinstInst_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  ren_exp xi_type xi_prog xi_exp =
  subst_exp (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
    (funcomp (var_exp) xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_exp xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
            (fun n => eq_refl) (fun n => eq_refl) x)).
Qed.

Lemma rinstInst_spec (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  ren_spec xi_type xi_prog xi_exp =
  subst_spec (funcomp (var_type) xi_type) (funcomp (var_prog) xi_prog)
    (funcomp (var_exp) xi_exp).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          rinst_inst_spec xi_type xi_prog xi_exp _ _ _ (fun n => eq_refl)
            (fun n => eq_refl) (fun n => eq_refl) x)).
Qed.

Lemma instId_exp : subst_exp (var_type) (var_prog) (var_exp) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_exp (var_type) (var_prog) (var_exp) (fun n => eq_refl)
            (fun n => eq_refl) (fun n => eq_refl) (id x))).
Qed.

Lemma instId_spec : subst_spec (var_type) (var_prog) (var_exp) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x =>
          idSubst_spec (var_type) (var_prog) (var_exp) (fun n => eq_refl)
            (fun n => eq_refl) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_exp : @ren_exp id id id = id.
Proof.
exact (eq_trans (rinstInst_exp (id _) (id _) (id _)) instId_exp).
Qed.

Lemma rinstId_spec : @ren_spec id id id = id.
Proof.
exact (eq_trans (rinstInst_spec (id _) (id _) (id _)) instId_spec).
Qed.

Lemma varL_exp (sigma_type : nat -> type) (sigma_prog : nat -> prog)
  (sigma_exp : nat -> exp) :
  funcomp (subst_exp sigma_type sigma_prog sigma_exp) (var_exp) = sigma_exp.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_exp (xi_type : nat -> nat) (xi_prog : nat -> nat)
  (xi_exp : nat -> nat) :
  funcomp (ren_exp xi_type xi_prog xi_exp) (var_exp) =
  funcomp (var_exp) xi_exp.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma renRen'_term (xi_term : nat -> nat) (zeta_term : nat -> nat) :
  funcomp (ren_term zeta_term) (ren_term xi_term) =
  ren_term (funcomp zeta_term xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_term xi_term zeta_term n)).
Qed.

Lemma renRen'_form (xi_term : nat -> nat) (zeta_term : nat -> nat) :
  funcomp (ren_form zeta_term) (ren_form xi_term) =
  ren_form (funcomp zeta_term xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renRen_form xi_term zeta_term n)).
Qed.

Lemma renSubst'_term (xi_term : nat -> nat) (tau_term : nat -> term) :
  funcomp (subst_term tau_term) (ren_term xi_term) =
  subst_term (funcomp tau_term xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_term xi_term tau_term n)).
Qed.

Lemma renSubst'_form (xi_term : nat -> nat) (tau_term : nat -> term) :
  funcomp (subst_form tau_term) (ren_form xi_term) =
  subst_form (funcomp tau_term xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => renSubst_form xi_term tau_term n)).
Qed.

Lemma substRen'_term (sigma_term : nat -> term) (zeta_term : nat -> nat) :
  funcomp (ren_term zeta_term) (subst_term sigma_term) =
  subst_term (funcomp (ren_term zeta_term) sigma_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_term sigma_term zeta_term n)).
Qed.

Lemma substRen'_form (sigma_term : nat -> term) (zeta_term : nat -> nat) :
  funcomp (ren_form zeta_term) (subst_form sigma_term) =
  subst_form (funcomp (ren_term zeta_term) sigma_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substRen_form sigma_term zeta_term n)).
Qed.

Lemma substSubst'_term (sigma_term : nat -> term) (tau_term : nat -> term) :
  funcomp (subst_term tau_term) (subst_term sigma_term) =
  subst_term (funcomp (subst_term tau_term) sigma_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_term sigma_term tau_term n)).
Qed.

Lemma substSubst'_form (sigma_term : nat -> term) (tau_term : nat -> term) :
  funcomp (subst_form tau_term) (subst_form sigma_term) =
  subst_form (funcomp (subst_term tau_term) sigma_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun n => substSubst_form sigma_term tau_term n)).
Qed.

Lemma rinstInst_term (xi_term : nat -> nat) :
  ren_term xi_term = subst_term (funcomp (var_term) xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_term xi_term _ (fun n => eq_refl) x)).
Qed.

Lemma rinstInst_form (xi_term : nat -> nat) :
  ren_form xi_term = subst_form (funcomp (var_term) xi_term).
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => rinst_inst_form xi_term _ (fun n => eq_refl) x)).
Qed.

Lemma instId_term : subst_term (var_term) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_term (var_term) (fun n => eq_refl) (id x))).
Qed.

Lemma instId_form : subst_form (var_term) = id.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => idSubst_form (var_term) (fun n => eq_refl) (id x))).
Qed.

Lemma rinstId_term : @ren_term id = id.
Proof.
exact (eq_trans (rinstInst_term (id _)) instId_term).
Qed.

Lemma rinstId_form : @ren_form id = id.
Proof.
exact (eq_trans (rinstInst_form (id _)) instId_form).
Qed.

Lemma varL_term (sigma_term : nat -> term) :
  funcomp (subst_term sigma_term) (var_term) = sigma_term.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Lemma varLRen_term (xi_term : nat -> nat) :
  funcomp (ren_term xi_term) (var_term) = funcomp (var_term) xi_term.
Proof.
exact (FunctionalExtensionality.functional_extensionality _ _
         (fun x => eq_refl)).
Qed.

Ltac asimpl_fext' := repeat (first
                      [ progress rewrite ?substSubst_form_pointwise
                      | progress rewrite ?substSubst_form
                      | progress rewrite ?substSubst_term_pointwise
                      | progress rewrite ?substSubst_term
                      | progress rewrite ?substRen_form_pointwise
                      | progress rewrite ?substRen_form
                      | progress rewrite ?substRen_term_pointwise
                      | progress rewrite ?substRen_term
                      | progress rewrite ?renSubst_form_pointwise
                      | progress rewrite ?renSubst_form
                      | progress rewrite ?renSubst_term_pointwise
                      | progress rewrite ?renSubst_term
                      | progress rewrite ?renRen'_form_pointwise
                      | progress rewrite ?renRen_form
                      | progress rewrite ?renRen'_term_pointwise
                      | progress rewrite ?renRen_term
                      | progress rewrite ?substSubst_spec_pointwise
                      | progress rewrite ?substSubst_spec
                      | progress rewrite ?substSubst_exp_pointwise
                      | progress rewrite ?substSubst_exp
                      | progress rewrite ?substRen_spec_pointwise
                      | progress rewrite ?substRen_spec
                      | progress rewrite ?substRen_exp_pointwise
                      | progress rewrite ?substRen_exp
                      | progress rewrite ?renSubst_spec_pointwise
                      | progress rewrite ?renSubst_spec
                      | progress rewrite ?renSubst_exp_pointwise
                      | progress rewrite ?renSubst_exp
                      | progress rewrite ?renRen'_spec_pointwise
                      | progress rewrite ?renRen_spec
                      | progress rewrite ?renRen'_exp_pointwise
                      | progress rewrite ?renRen_exp
                      | progress rewrite ?substSubst_index_pointwise
                      | progress rewrite ?substSubst_index
                      | progress rewrite ?substRen_index_pointwise
                      | progress rewrite ?substRen_index
                      | progress rewrite ?renSubst_index_pointwise
                      | progress rewrite ?renSubst_index
                      | progress rewrite ?renRen'_index_pointwise
                      | progress rewrite ?renRen_index
                      | progress rewrite ?substSubst_prog_pointwise
                      | progress rewrite ?substSubst_prog
                      | progress rewrite ?substRen_prog_pointwise
                      | progress rewrite ?substRen_prog
                      | progress rewrite ?renSubst_prog_pointwise
                      | progress rewrite ?renSubst_prog
                      | progress rewrite ?renRen'_prog_pointwise
                      | progress rewrite ?renRen_prog
                      | progress rewrite ?substSubst_type_pointwise
                      | progress rewrite ?substSubst_type
                      | progress rewrite ?substRen_type_pointwise
                      | progress rewrite ?substRen_type
                      | progress rewrite ?renSubst_type_pointwise
                      | progress rewrite ?renSubst_type
                      | progress rewrite ?renRen'_type_pointwise
                      | progress rewrite ?renRen_type
                      | progress rewrite ?varLRen_term
                      | progress rewrite ?varL_term
                      | progress rewrite ?rinstId_form
                      | progress rewrite ?rinstId_term
                      | progress rewrite ?instId_form
                      | progress rewrite ?instId_term
                      | progress rewrite ?substSubst'_form
                      | progress rewrite ?substSubst'_term
                      | progress rewrite ?substRen'_form
                      | progress rewrite ?substRen'_term
                      | progress rewrite ?renSubst'_form
                      | progress rewrite ?renSubst'_term
                      | progress rewrite ?renRen'_form
                      | progress rewrite ?renRen'_term
                      | progress rewrite ?varLRen_exp
                      | progress rewrite ?varL_exp
                      | progress rewrite ?rinstId_spec
                      | progress rewrite ?rinstId_exp
                      | progress rewrite ?instId_spec
                      | progress rewrite ?instId_exp
                      | progress rewrite ?substSubst'_spec
                      | progress rewrite ?substSubst'_exp
                      | progress rewrite ?substRen'_spec
                      | progress rewrite ?substRen'_exp
                      | progress rewrite ?renSubst'_spec
                      | progress rewrite ?renSubst'_exp
                      | progress rewrite ?renRen'_spec
                      | progress rewrite ?renRen'_exp
                      | progress rewrite ?rinstId_index
                      | progress rewrite ?instId_index
                      | progress rewrite ?substSubst'_index
                      | progress rewrite ?substRen'_index
                      | progress rewrite ?renSubst'_index
                      | progress rewrite ?renRen'_index
                      | progress rewrite ?varLRen_prog
                      | progress rewrite ?varL_prog
                      | progress rewrite ?rinstId_prog
                      | progress rewrite ?instId_prog
                      | progress rewrite ?substSubst'_prog
                      | progress rewrite ?substRen'_prog
                      | progress rewrite ?renSubst'_prog
                      | progress rewrite ?renRen'_prog
                      | progress rewrite ?varLRen_type
                      | progress rewrite ?varL_type
                      | progress rewrite ?rinstId_type
                      | progress rewrite ?instId_type
                      | progress rewrite ?substSubst'_type
                      | progress rewrite ?substRen'_type
                      | progress rewrite ?renSubst'_type
                      | progress rewrite ?renRen'_type
                      | progress
                         unfold up_term_term, upRen_term_term, up_exp_exp,
                          up_exp_prog, up_exp_type, up_prog_exp, up_type_exp,
                          upRen_exp_exp, upRen_exp_prog, upRen_exp_type,
                          upRen_prog_exp, upRen_type_exp, up_prog_prog,
                          up_prog_type, up_type_prog, upRen_prog_prog,
                          upRen_prog_type, upRen_type_prog, up_type_type,
                          upRen_type_type, up_ren
                      | progress
                         cbn[subst_form subst_term ren_form ren_term
                            subst_spec subst_exp ren_spec ren_exp subst_index
                            ren_index subst_prog ren_prog subst_type
                            ren_type]
                      | fsimpl_fext ]).

Ltac asimpl_fext := check_no_evars; repeat try unfold_funcomp;
                     repeat
                      unfold VarInstance_type, Var, ids, Ren_type, Ren1,
                       ren1, Up_type_type, Up_type, up_type, Subst_type,
                       Subst1, subst1, VarInstance_prog, Var, ids, Ren_prog,
                       Ren2, ren2, Up_type_prog, Up_prog, up_prog,
                       Up_prog_type, Up_type, up_type, Up_prog_prog, Up_prog,
                       up_prog, Subst_prog, Subst2, subst2, Ren_index, Ren1,
                       ren1, Subst_index, Subst1, subst1, VarInstance_exp,
                       Var, ids, Ren_exp, Ren3, ren3, Ren_spec, Ren3, ren3,
                       Up_type_exp, Up_exp, up_exp, Up_prog_exp, Up_exp,
                       up_exp, Up_exp_type, Up_type, up_type, Up_exp_prog,
                       Up_prog, up_prog, Up_exp_exp, Up_exp, up_exp,
                       Subst_exp, Subst3, subst3, Subst_spec, Subst3, subst3,
                       VarInstance_term, Var, ids, Ren_term, Ren1, ren1,
                       Ren_form, Ren1, ren1, Up_term_term, Up_term, up_term,
                       Subst_term, Subst1, subst1, Subst_form, Subst1, subst1
                       in *; asimpl_fext'; repeat try unfold_funcomp.

Tactic Notation "asimpl_fext" "in" hyp(J) := revert J; asimpl_fext; intros J.

Tactic Notation "auto_case_fext" := auto_case ltac:(asimpl_fext; cbn; eauto).

Ltac substify_fext := auto_unfold; try repeat erewrite ?rinstInst_form;
                       try repeat erewrite ?rinstInst_term;
                       try repeat erewrite ?rinstInst_spec;
                       try repeat erewrite ?rinstInst_exp;
                       try repeat erewrite ?rinstInst_index;
                       try repeat erewrite ?rinstInst_prog;
                       try repeat erewrite ?rinstInst_type.

Ltac renamify_fext := auto_unfold; try repeat erewrite <- ?rinstInst_form;
                       try repeat erewrite <- ?rinstInst_term;
                       try repeat erewrite <- ?rinstInst_spec;
                       try repeat erewrite <- ?rinstInst_exp;
                       try repeat erewrite <- ?rinstInst_index;
                       try repeat erewrite <- ?rinstInst_prog;
                       try repeat erewrite <- ?rinstInst_type.

End Fext.

Module Extra.

Import Core.

#[global]Hint Opaque subst_form: rewrite.

#[global]Hint Opaque subst_term: rewrite.

#[global]Hint Opaque ren_form: rewrite.

#[global]Hint Opaque ren_term: rewrite.

#[global]Hint Opaque subst_spec: rewrite.

#[global]Hint Opaque subst_exp: rewrite.

#[global]Hint Opaque ren_spec: rewrite.

#[global]Hint Opaque ren_exp: rewrite.

#[global]Hint Opaque subst_index: rewrite.

#[global]Hint Opaque ren_index: rewrite.

#[global]Hint Opaque subst_prog: rewrite.

#[global]Hint Opaque ren_prog: rewrite.

#[global]Hint Opaque subst_type: rewrite.

#[global]Hint Opaque ren_type: rewrite.

End Extra.

Module interface.

Export Core.

Export Fext.

Export Extra.

End interface.

Export interface.

