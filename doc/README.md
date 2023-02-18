## Errors

1. Absolute error for multiplying numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) * (n * 2^e2 + 2^(e2 - p)) - m * 2^e1 * n * 2^e2` <= (does not exceed) **2 ^ (e1 + e2 - p + 2)**.
Error's exponent grows with sequential multiplications of m by different numbers n by 1 + e2 each iteration.

2. Absolute error for dividing numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = m * 2^e1 / (n * 2^e2) - (m * 2^e1 - 2^(e1 - p)) / (n * 2^e2 + 2^(e2 - p))` <= (does not exceed) **2 ^ (e1 - e2 - p + 2)**.
Error's exponent grows with sequential divisions of m by different numbers n by 2 - e2 each iteration.

3. Absolute error for subtraction of numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) - (n * 2^e2 - 2^(e2 - p)) - (m * 2^e1 - n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + 2)**.

4. Absolute error for addition of numbers with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= n < 1`, `0.5 <= m < 1` - mantissas.

Error `err = (m * 2^e1 + 2^(e1 - p)) + (n * 2^e2 + 2^(e2 - p)) - (m * 2^e1 + n * 2^e2)` <= (does not exceed) **2 ^ (max(e1, e2) - p + 2)**.

5. Absolute error for square root of a number with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= m < 1` is mantissa.

Error `err = sqrt(m * 2^e + 2^(e - p)) - sqrt(m * 2^e)` <= (does not exceed) **2 ^ (ceil(e/2) + 1 - p)** .

6. Absolute error for nth root of a number with precision `p` and maximum error of `2^(-p)` (i.e. 1 ulp) using rounding mode `None`, where

`0.5 <= m < 1` is mantissa.

Error `err = nroot(m * 2^e + 2^(e - p)) - nroot(m * 2^e)` <= (does not exceed) **2 ^ (ceil(e/n) + 1 - p)** .
