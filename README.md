# UPDATE:
Please move to the new package [GeometricCADv2](https://github.com/xiaxueqaq/GeometricCADv2) for a more efficient and simpler implementation.

# GeometricCAD
A geometrical algorithm of cylindrical algebraic decomposition based on Grothendieck's Generic Freeness Lemma and Parametric Hermite Quadratic Form.

# Dependency
- Mathematica 12
- Singular
- Singular Interface to Mathematica (available at [xiaxueqaq/Mathematica-Interface-of-Singular](https://github.com/xiaxueqaq/Mathematica-Interface-of-Singular))

# Install
1. Make sure that Singular is installed. In Windows 10, it should be installed with WSL (Windows Subsytem for Linux).
2. Install Singular Interface to Mathematica, you may follow the instruction in the above link. It is pretty easy, just copy the source code to somewhere Mathematica can automatically find.
3. Download `GeometricCAD.wl`.
4. You can open it and run all codes so you can use the functions in it.

# Usage
Although there are many public functions, only two are on the highest level (to users).

`GeometricCylindricalDecomposition[L,x]`
$L$ is a list of basic constructible sets, $x$ is the set of variables, the result is a cylindrical algebraic decomposition of $L$, each cell is represented by a sample point.

`GeometricCylindricalDecompositionEqs[L,eqs,x]`
$L$ is a list of basic constructible sets, $eqs$ are the equational constraints, $x$ is the set of variables, the result is a cylindrical algebraic decomposition of $L\cap V(eqs)$, each cell is represented by a sample point.

# Example
`GeometricCylindricalDecomposition[{{{x^3 + p x + q}, 1}}, {p, q, x}]`. 

The result is `{{{-1}, {0}, {1}}, {{-1, -1}, {-1, -(2/(3 Sqrt[3]))}, {-1, 0}, {-1, 
   2/(3 Sqrt[3])}, {-1, 1}, {0, -1}, {0, 0}, {0, 1}, {1, 
   0}}, {{-1, -1, 0}, {-1, -1, Root[-1 - # + #^3& , 1, 0]}, {-1, -1, 
   2}, {-1, -(2/(3 Sqrt[3])), -2}, {-1, -(2/(3 Sqrt[3])), 
   1/(2 Sqrt[3]) - Sqrt[3]/2}, {-1, -(2/(3 Sqrt[3])), 
   0}, {-1, -(2/(3 Sqrt[3])), 
   1/(2 Sqrt[3]) + Sqrt[3]/2}, {-1, -(2/(3 Sqrt[3])), 2}, {-1, 
   0, -2}, {-1, 0, -1}, {-1, 0, -(1/2)}, {-1, 0, 0}, {-1, 0, 1/
   2}, {-1, 0, 1}, {-1, 0, 2}, {-1, 2/(3 Sqrt[3]), -2}, {-1, 2/(
   3 Sqrt[3]), -(1/(2 Sqrt[3])) - Sqrt[3]/2}, {-1, 2/(3 Sqrt[3]), 
   0}, {-1, 2/(3 Sqrt[3]), -(1/(2 Sqrt[3])) + Sqrt[3]/2}, {-1, 2/(
   3 Sqrt[3]), 2}, {-1, 1, -2}, {-1, 1, Root[
   1 - # + #^3& , 1, 0]}, {-1, 1, 0}, {0, -1, 0}, {0, -1, 1}, {0, -1, 
   2}, {0, 0, -1}, {0, 0, 0}, {0, 0, 1}, {0, 1, -2}, {0, 1, -1}, {0, 
   1, 0}, {1, 0, -1}, {1, 0, 0}, {1, 0, 1}}}`. 
   
   You can refer to Examples-in-Paper folder or Experiments folder for more examples. 
