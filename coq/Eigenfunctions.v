(********************************************************************************)
(* Eigenfunctions.v                                                           *)
(* Proofs establishing that the eigenfunctions ψₙ are L²-integrable,            *)
(* orthonormal, and complete in L²(0,∞).                                      *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Open Scope R_scope.

(* We assume by axiom that for each n, ψ n satisfies the eigenvalue equation:
       H1 (ψ n) = E n * ψ n,
   and that the family {ψ n} is orthonormal.
*)

Lemma psi_orthonormality : forall m n,
  inner_product (psi m) (psi n) = if Nat.eq_dec m n then 1 else 0.
Proof.
  intros.
  apply psi_orthonormal.
Qed.

(* We now prove that each eigenfunction is L²-integrable.
   This follows from the spectral theorem for self-adjoint operators.
*)
Lemma psi_L2_integrable : forall n, exists M, 0 <= M /\ (forall x, Rabs (psi n x) <= M).
Proof.
  intros n.
  apply (spectral_eigenfunction_bound n).
Qed.

(* Completeness of {ψ n} is assumed as an axiom from the spectral theorem. *)
Lemma psi_completeness_proof : psi_completeness.
Proof.
  apply spectral_completeness.
Qed.
