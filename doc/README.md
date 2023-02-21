## Errors

1. Absolute error for multiplying numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) * (n * 2^e2 + 2^(e2 - p)) - m * 2^e1 * n * 2^e2` <= (does not exceed) **2 ^ (e1 + e2 - p + 2)**.

For k > 0 `err = (m * 2^e1 + 2^(e1 - p + k)) * (n * 2^e2 + 2^(e2 - p)) - m * 2^e1 * n * 2^e2` <= (does not exceed) **2 ^ (e1 + e2 - p + k + 1)**.

2. Absolute error for dividing numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = m * 2^e1 / (n * 2^e2) - (m * 2^e1 - 2^(e1 - p)) / (n * 2^e2 + 2^(e2 - p))` <= (does not exceed) **2 ^ (e1 - e2 - p + 3)**.

For k > 0 `err = m * 2^e1 / (n * 2^e2) - (m * 2^e1 - 2^(e1 - p + k)) / (n * 2^e2 + 2^(e2 - p))` <= (does not exceed) **2 ^ (e1 - e2 - p + k + 3)**.

And `err = m * 2^e1 / (n * 2^e2) - (m * 2^e1 - 2^(e1 - p)) / (n * 2^e2 + 2^(e2 - p + k))` <= (does not exceed) **2 ^ (e1 - e2 - p + k + 3)**.

3. Absolute error for subtraction of numbers with the same sign with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) - (n * 2^e2 - 2^(e2 - p)) - (m * 2^e1 - n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + 2)**.

For k > 0 `err = (m * 2^e1 + 2^(e1 - p + k)) - (n * 2^e2 - 2^(e2 - p)) - (m * 2^e1 - n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + k + 1)**.

For k > 0 `err = (m * 2^e1 + 2^(e1 - p + k)) - (n * 2^e2 - 2^(e2 - p)) - (m * 2^e1 - n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + k + 2)**.

4. Absolute error for addition of numbers with the same sign with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) + (n * 2^e2 + 2^(e2 - p)) - (m * 2^e1 + n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + 1)**.

For k > 0 `err = (m * 2^e1 + 2^(e1 - p + k)) + (n * 2^e2 + 2^(e2 - p)) - (m * 2^e1 + n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + k + 1)**.

5. Absolute error for square root of a number with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= m < 1` is mantissa.

Error `err = sqrt(m * 2^e + 2^(e - p)) - sqrt(m * 2^e)` <= (does not exceed) **2 ^ (ceil(e/2) + 1 - p)** .

6. Absolute error for nth root of a number with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= m < 1` is mantissa.

Error `err = nroot(m * 2^e + 2^(e - p)) - nroot(m * 2^e)` <= (does not exceed) **2 ^ (ceil(e/n) + 1 - p)**.

7. Error for series of sin, cos and sinh.

Error of Maclaurin series M(x) of a function f(x) for x < 1 in which absolute value of the function derivatives near 0 never exceeds 1 need to be estimated only for several first parts of the series.

Proof.

`err = M(m*2^e + 2^(e-p)) - M(m*2^e) = 2^e * M(m + 2^p) - M(m)`.

`0.5 <= m < 1` and `e <= 0`.

For simplisity assume e = 0 and the absolute value of nth derivative is 1.

Then series look like:

`M(x) = f(0) + x + x^2/2! + x^3/3! + ... + x^n/n!`

From binomial formula `(1 + x)^n = sum(Bk * x^k)` follows if x = 1 then sum of binomail coefficients is `2^n = sum(Bk)` (1).

Then `(m + 2^(-p))^n < = (1 + 2^(-p))^n = sum(Bk * 2^(-p * k))`, assuming m = 1.

Since we subtract `m^n` from `(m + 2^(-p))^n` to compute the absolute error, k > 0.

Then using (1) we get `sum(Bk * 2^(-p * k)) < sum(Bk * 2^(-p)) = 2^(n - p)`.

From Stirling's approximation `n! > (n/e) ^ n` 
follows `2^(n - p) / n! < 2^(n - p) * (e/n)^n = 2^(-p) * (2 * e / n)^n`.

The residual error of the series can be received from Lagrange's error bound,
and it is smaller than `2^(-p) * (2 * e / (n + 1))^(n + 1)`.

For n+1 parts of the series `err < 2^(-p) * sum((2 * e / k)^k), k=1..n+1`.

Starting from k = 6 `sum((2 * e / k)^k) < 1` and `err < 2^(-p)`.

8. Error for atan, atanh series.

`atan(x) = x - x^3/3 + x^5/5 - ...`

`atanh(x) = x + x^3/3 + x^5/5 + ...`

Assume, the series `x - a3 * x^3 + a5 * x^5 - ...` is computed directly, and x contains error less than `2^(-p)`:

`a3`, `a5`,... have error less than `2^(-p)` since they are the result of division of 1 by the exact number 3, 5, 7,... 
and their value is smaller than 0.5 by definition.

If `x = m*2^e`, where `0.5 <= m < 1` and `e = -3`, then absolute error relative to 1 for atanh:

`2^(-p-3) + 2^(-p-9+3) + 2^(-p-15+5) + ... < 2(^-p-2)` or less than `2^(-p+1)` relative to x. The same is true for e < -3.

For atan error is `2^(-p+2)`, since the first subtraction can cause borrow.