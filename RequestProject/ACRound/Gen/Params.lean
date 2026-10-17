module

public import RequestProject.ACRound.Build

/-!
# Parameters of the round circuit family

`GCst` collects the constants determining the round circuit for inputs of length `n`:
`(n + 1)^e` queries per round, `c · (⌊log₂ n⌋ + 1)^k` rounds, query words of length at most
`A · (n + 1)^A`, and blocks of size `cB · (L + 1)^cB + 1` (`cB` bounds the size of the oracle
circuits).
-/

@[expose] public section

namespace PathChecking

/-- Constants of the round circuit family. -/
structure GCst where
  e : ℕ
  c : ℕ
  k : ℕ
  A : ℕ
  cB : ℕ

namespace GCst

variable (G : GCst)

/-- Queries per round. -/
def Nq (n : ℕ) : ℕ := (n + 1) ^ G.e

/-- Number of rounds. -/
def R (n : ℕ) : ℕ := G.c * (Nat.log 2 n + 1) ^ G.k

/-- Bound on the query lengths. -/
def L (n : ℕ) : ℕ := G.A * (n + 1) ^ G.A

/-- Block size. -/
def S (n : ℕ) : ℕ := G.cB * (G.L n + 1) ^ G.cB + 1

/-- The layout for inputs of length `n`. -/
def lay (CB : ℕ → Circuit) (n : ℕ) : Lay := ⟨n, G.Nq n, G.R n, G.L n, G.S n, CB⟩

end GCst

end PathChecking
