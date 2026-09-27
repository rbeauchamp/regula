/-! An unconditional pointwise proof over the complete input domain, including its proof
argument. -/
def fixtures_pointwise_impl (n : Nat) (_h : 0 < n) : Nat := 2 * n
@[implemented_by fixtures_pointwise_impl]
def fixtures_pointwise_reference (n : Nat) (_h : 0 < n) : Nat := n + n
theorem fixtures_pointwise_correspondence (n : Nat) (h : 0 < n) :
    fixtures_pointwise_reference n h = fixtures_pointwise_impl n h := (Nat.two_mul n).symm
