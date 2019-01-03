This repsitory contains some proofs I need for formalizing lp-spaces. In particular it contains a proof of Young's inequality which is the main tool for proving Hoelder's and Minkowskis inequalities.
The inequality is proven using the tools provided by Coq's standard library and Coquelicot. The files have only been tested with Coq version 8.8.2.
Youngs inequality states that for all positive a, b and p q hoelder associates it holds that a * b <= a^p/p + b^q/q and is important due to its applications in functional analysis.
The power-function from the standard library is defined as Rpower a p := exp (p * ln a) and thus unspecified when a is zero.
To mend this, the file defines a new function Rabs_power, that is equal to exp (p * ln |a|) and zero when a is zero. This should be the correct definition for the applications in lp theory.
Since this function may be of use separately, some lemmas about it are proven.
The file then lists a definition of what it means for a function to be strictly concave and a proof the logaritm function is strictly concave using the characterization that a function on the real numbers is strictly concave if and only if its derivative is strictly decreasing.
The later may be of separate interest and the proof can be found in the file "concave.v".
Another thing of separate interest is a restatement of the mean value theorem.
If I am not mistaken, the version currently included in the standard library makes a slightly too strong continuity assumption, the version in the mean_value_theorem file removes this.
