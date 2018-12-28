The files in this repository prove Young's inequality using the tools provided by Coq's standard library. The files have only been tested with Coq version 8.8.2.
Youngs inequality states that for all positive a, b and p q hoelder associates it holds that a * b <= a^p/p + b^q/q and is important due to its applications in functional analysis.
The power-function from the standard library is defined as Rpower a p := exp (p * ln a) and thus unspecified when a is zero.
To mend this, the file defines a new function Rabs_power, that is equal to exp (p * ln |a|) and zero when a is zero. This should be the correct definition for the applications in lp theory.
Since this function may be of use separately, some lemmas about it are proven.
The file then lists a definition of what it means for a function to be strictly concave and a proof the logaritm function is strictly concave using the characterization that a function on the real numbers is strictly concave if and only if its derivative is strictly decreasing.
This part of the proof should be fairly easy to generalize, however, the current version of the mean value theorem from the standard library makes slightly too strong assumptions about the continuity of the involved functions and I'd rather wait for this to be fixed before investing more work.
Finally there is a separate file where a proof is specified that the Rabs_power function is continuous in x whenever p is strictly bigger than zero.
The reason for this to be in a separate file is that it introduces Coquelicot as an additional dependency.