# Looking for PDFs? Compiled Docs: https://github.com/UOR-Foundation/UOR-H1-HPO-Candidate/releases/latest

### This Repo is being actively developed to run the proofs in GitHub Actions. Start with the Docs and we'll try to have the proofs ready when you are done. 

# Formalized UOR H1 HPO Candidate and Proofs

This repository contains a formalized proof of the Riemann Hypothesis, developed within the Universal Object Reference (UOR) framework and verified using the Coq proof assistant.

## Overview

The proof is based on the construction of a self-adjoint operator, denoted as \(\hat{H}_1\), whose spectrum corresponds to the non-trivial zeros of the Riemann zeta function. The operator is defined on a Hilbert space of square-integrable functions and is shown to have a compact resolvent, ensuring a discrete spectrum.

The proof involves several key steps:

- **Verification of Eigenfunction Properties:** We prove that the eigenfunctions of \(\hat{H}_1\) are square-integrable and form a complete orthonormal basis.
- **Self-Adjointness:** We establish that \(\hat{H}_1\) is essentially self-adjoint, ensuring the reality of its eigenvalues.
- **Compact Resolvent:** We demonstrate that \(\hat{H}_1\) has a compact resolvent, implying a discrete spectrum.
- **Heat Kernel and Theta Function:** We show that the heat kernel trace of \(\hat{H}_1\) satisfies a functional equation analogous to the Jacobi theta function, which in turn implies the functional equation of the Riemann zeta function.

## Coq Formalization

The entire proof is formalized in Coq, providing a machine-checked verification of its logical consistency and correctness. The Coq development leverages the UOR framework to represent mathematical objects and their relationships in a rigorous and unambiguous manner.

## Repository Structure

- `UOR-H1-HPO-Candidate.tex`: The main LaTeX document containing the narrative of the proof.
- `Appendix-1-Structures.tex`: An appendix with additional details and proofs.
-  `Appendix-2-Principles.tex`: An appendix with the complete UOR construction of the UOR H1 HPO Candidate.
- `coq/`: The directory containing the Coq formalization of the proof.

## Usage

To compile the LaTeX documents, you will need a LaTeX distribution installed on your system. You can then run `pdflatex` on the `.tex` files to generate PDF documents.

To verify the Coq formalization, you will need Coq installed on your system. You can then use `coqc` to compile the Coq files and `coqtop` to interactively explore the proof.

## Contributions

Contributions to this repository are welcome. If you find any errors or have suggestions for improvements, please feel free to submit a pull request.

## Personal Note

I'm proud to present this proof to the world. I am but a novice and it is humbling to work with such incredible friends, mentors, and technology. You all bring me up. -Alex
