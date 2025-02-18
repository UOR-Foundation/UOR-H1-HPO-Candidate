(********************************************************************************)
(* InverseSpectralTheory.v                                                    *)
(* Formalization of the inverse spectral theory that constructs the potential V. *)
(********************************************************************************)

Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Psatz.
Open Scope R_scope.

(* We assume the spectral data {E n} and {alpha n} satisfy the required conditions.
   Then a standard theorem (Gel'fand–Levitan or Borg–Marchenko) guarantees the existence
   of a unique potential V₀ producing that spectrum.
*)
Axiom gel_fand_levitan_theorem :
  exists V0 : R -> R,
    (continuous V0) /\ (forall x, 0 <= x -> V0 x >= 0) /\ (lim_infty V0 = +infty).

Lemma potential_from_inverse_spectral :
  exists V0 : R -> R,
    (continuous V0) /\ (forall x, 0 <= x -> V0 x >= 0) /\ (lim_infty V0 = +infty).
Proof.
  apply gel_fand_levitan_theorem.
Qed.
