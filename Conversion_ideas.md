# Ideas for initial conversions between Lean and Macaulay2

|Lean gives|Macaulay returns|Notes|
|-|-|-|
|Integer| Factorisation||
|Polynomial| Factorisation|Coefficients TBD -- $\mathbb{Z}$?|
|Ideal|Gröbner basis| Ambient ring TBD -- $\mathbb{Z}[x_1, \ldots x_n]$?|
|(Ideal, polynomial)|Certificate for whether the polynomial belongs to the ideal|Lots to be determined!|
