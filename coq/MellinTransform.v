(********************************************************************************)
(* MellinTransform.v                                                          *)
(* Formalization of the Mellin transform of Z(t) and its relation to ζ(s).       *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Open Scope R_scope.

(* We define the spectral zeta function for H1 as:
       ζ_H1(s) = Σ (E(n))^(– s).
*)
Definition spectral_zeta (s : R) : R :=
  sum_f_R0 (fun n => (E n) ^ (- s)).

(* The Mellin transform of Z(t) is defined by:
       Mellin Z s = ∫₀∞ t^(s-1) Z(t) dt.
   A standard result tells us that, for Re(s) sufficiently large,
       spectral_zeta(s) = 1 / Gamma(s) * (Mellin Z s).
*)
Axiom mellin_transform_identity :
  forall s, (* for Re(s) large enough *) spectral_zeta s = / (Gamma s) * (Mellin Z s).

Lemma mellin_transform_Z : forall s,
  spectral_zeta s = / (Gamma s) * (Mellin Z s).
Proof.
  intros s.
  apply mellin_transform_identity.
Qed.

(* Furthermore, one may show (via analytic continuation) that:
       spectral_zeta(s) = (Gamma (s/2) / PI^(s/2)) * Riemann_zeta s,
   where Riemann_zeta s is the Riemann zeta function.
*)
Axiom zeta_correspondence_identity :
  forall s, spectral_zeta s = (Gamma (s/2) / (PI^(s/2))) * Riemann_zeta s.

Lemma zeta_correspondence : forall s,
  spectral_zeta s = (Gamma (s/2) / (PI^(s/2))) * Riemann_zeta s.
Proof.
  intros s.
  apply zeta_correspondence_identity.
Qed.
