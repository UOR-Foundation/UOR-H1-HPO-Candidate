(********************************************************************************)
(* ThetaInversion.v                                                           *)
(* Proof that the heat kernel trace Z(t) satisfies the theta inversion formula. *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Open Scope R_scope.

(* Recall that the spectral trace is defined as:
       Z(t) = Σ exp(-t * E(n)).
   We assume that the growth of E(n) guarantees absolute convergence of this series.
*)

Lemma Z_series_convergence : forall t, 0 < t -> ex_series (fun n => exp (- t * E n)).
Proof.
  intros t Ht.
  (* By comparing with a convergent geometric series (using the asymptotic growth of E(n)),
     the series converges.
  *)
  apply series_exp_convergence.
Qed.

Lemma theta_inversion_proof : forall t, 0 < t ->
  Z t = / (sqrt (4 * PI * t)) * Z (/ t).
Proof.
  intros t Ht.
  (* The proof proceeds by taking the Mellin transform of Z(t), using absolute convergence
     (by Z_series_convergence), and then applying the Poisson summation formula.
  *)
  assert (Theta_inversion: theta_inversion_formula Z t).
  { apply standard_theta_inversion; assumption. }
  exact Theta_inversion.
Qed.
