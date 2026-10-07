#!/usr/bin/env python3
"""Emit denominator-cleared SOS data checked by Lean kernel polynomial reduction."""
from lean_source import write_lean
from pathlib import Path
import json, math
from fractions import Fraction as Q
from itertools import permutations, combinations
ROOT=Path(__file__).resolve().parents[1]
def rat(x):
 x=Q(x)
 return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator} : ℝ)'
def sos(cert):
 result=[]
 for block,E,K in zip(cert['blocks'],cert['E'],cert['K']):
  E=[[Q(x) for x in r] for r in E]; K=[[Q(x) for x in r] for r in K]; n=len(K)
  if len(block)==4 and (all(a//4==b//4 and a!=b for a,b in block) or all(a%4==b%4 and a!=b for a,b in block)):
   assert E==[[Q(-1),Q(-1),Q(-1)],[Q(1),Q(0),Q(0)],[Q(0),Q(1),Q(0)],[Q(0),Q(0),Q(1)]]
   K=[[x-Q(1,1000)*(3 if i==j else -1) for j,x in enumerate(row)] for i,row in enumerate(K)]
  for i in range(n):
   d=K[i][i]; assert d>0
   v=[E[j][i]+sum(K[i][k]/d*E[j][k] for k in range(i+1,n)) for j in range(len(E))]
   result.append((d,v,block))
   for j in range(i+1,n):
    for k in range(j,n):
     K[j][k]-=K[j][i]*K[i][k]/d; K[k][j]=K[j][k]
 return result
def sum_expr(expressions):
 expressions=list(expressions)
 if not expressions: return const_expr(0)
 result=expressions[0]
 for expression in expressions[1:]: result=f'(Expr.add {result} {expression})'
 return result

def product_expr(expressions):
 expressions=list(expressions)
 if not expressions: return const_expr(1)
 result=expressions[0]
 for expression in expressions[1:]: result=f'(Expr.mul {result} {expression})'
 return result

def const_expr(q):
 q=Q(q)
 assert q.denominator==1
 return f'(Expr.c ({q.numerator} : ℤ))'

def variable_expr(i): return f'(Expr.x {i})'
def square_expr(e): return f'(Expr.sq {e})'
def minus_expr(e,f): return f'(Expr.sub {e} {f})'
def times_expr(e,f): return f'(Expr.mul {e} {f})'

def residual(cert, coefficient=rat):
 terms=[]
 for p,w in zip(permutations(range(4)),cert['weights']):
  terms.append(f'({coefficient(w)}) * ('+' * '.join(f'a {4*i+j}' for i,j in enumerate(p))+')')
 target=coefficient(Q(3,32))+' * ('+' + '.join(f'a {j} ^ 2' for j in range(16))+') ^ 2 - ('+' + '.join(terms)+')'
 defect_terms=[]
 for i,j in combinations(range(4),2):
  for k,l in combinations(range(4),2):
   defect_terms += [f'(a {4*i+k} * a {4*i+l} - a {4*j+k} * a {4*j+l}) ^ 2',
                    f'(a {4*i+k} * a {4*j+k} - a {4*i+l} * a {4*j+l}) ^ 2']
 return target+' - '+coefficient(Q(1,1000))+' * ('+' + '.join(defect_terms)+')'

def residual_expr(cert,scale):
 x=variable_expr
 target=minus_expr(times_expr(integer_const(scale*Q(3,32)),square_expr(sum_expr(square_expr(x(i)) for i in range(16)))),
  sum_expr(times_expr(integer_const(scale*Q(w)),product_expr(x(4*i+j) for i,j in enumerate(p)))
           for p,w in zip(permutations(range(4)),cert['weights'])))
 defect=[]
 for i,j in combinations(range(4),2):
  for k,l in combinations(range(4),2):
   defect += [square_expr(minus_expr(times_expr(x(4*i+k),x(4*i+l)),times_expr(x(4*j+k),x(4*j+l)))),
              square_expr(minus_expr(times_expr(x(4*i+k),x(4*j+k)),times_expr(x(4*i+l),x(4*j+l))))]
 return minus_expr(target,times_expr(integer_const(scale*Q(1,1000)),sum_expr(defect)))

def integral(x):
 x=Q(x); assert x.denominator==1; return str(x.numerator)
def integer_const(x):return f'(Expr.c ({integral(x)} : ℤ))'
def integer_cast(x):return f'(({integral(x)} : ℤ) : ℝ)'
def real_int(x):return f'({integral(x)} : ℝ)'

def emit(index, cert):
 squares=[]
 # Clear denominators in each quadratic; divide its weight by the square scale.
 for d,v,b in sos(cert):
  m=math.lcm(*(q.denominator for q in v))
  squares.append((d/(m*m),[q*m for q in v],b))
 # Clear all remaining weight and target denominators by one positive integer.
 D=math.lcm(32,1000,*(Q(w).denominator for w in cert['weights']),*(d.denominator for d,_,_ in squares))
 entries=[]
 for d,v,block in squares:
  e=sum_expr(times_expr(integer_const(c),times_expr(variable_expr(i),variable_expr(j))) for c,(i,j) in zip(v,block) if c)
  entries.append(f'(({integral(D*d)} : ℤ), {e})')
 expr=residual_expr(cert,D)
 cast_target=residual(cert,lambda q:integer_cast(D*Q(q)))
 real_target=residual(cert,lambda q:real_int(D*Q(q)))
 abstract=[f'm{i}' for i in range(24)]
 def abstract_residual(scale):
  def r(q): return rat(scale*Q(q))
  return f'{r(Q(3,32))} * s - ('+' + '.join(f'({r(w)}) * {m}' for w,m in zip(cert['weights'],abstract))+f') - {r(Q(1,1000))} * d'
 sqsum='('+' + '.join(f'a {j} ^ 2' for j in range(16))+') ^ 2'
 mons=['('+' * '.join(f'a {4*i+j}' for i,j in enumerate(p))+')' for p in permutations(range(4))]
 defects=[]
 for i,j in combinations(range(4),2):
  for k,l in combinations(range(4),2):
   defects.extend([f'(a {4*i+k} * a {4*i+l} - a {4*j+k} * a {4*j+l}) ^ 2',f'(a {4*i+k} * a {4*j+k} - a {4*i+l} * a {4*j+l}) ^ 2'])
 defect='('+' + '.join(defects)+')'
 square_list='[\n  '+',\n  '.join(entries)+'\n]'
 # Two private import chains bound cold-build concurrency without changing proofs.
 predecessor='' if index in (0,65) else f'import FourRow.Grams.G{index-1:03}\n'
 source=f'''module
public import FourRow.PolynomialCertificate
{predecessor}@[expose] public section
namespace FourRow
open PolynomialCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Positive integer multiple of the strengthened rational Gram residual. -/
def gramTarget{index:03} : Expr := {expr}
/-- Exact positive weighted squares after clearing rational denominators. -/
def gramSquares{index:03} : List (ℤ × Expr) := {square_list}
/-- Kernel reduction checks the exact sparse integer polynomial identity. -/
theorem gramIdentity{index:03} : fastnorm (rawexpand gramTarget{index:03}) = fastnorm (rawsquares gramSquares{index:03}) := by decide +kernel
/-- All integer square weights are nonnegative. -/
theorem gramPositive{index:03} : gramSquares{index:03}.all (fun s => decide (0 ≤ s.1)) = true := by decide +kernel

/-- Exact scalar identity returning from integer to rational coefficients. -/
theorem gramScale{index:03} (s d : ℝ) ({' '.join(abstract)} : ℝ) :
    {abstract_residual(D)} = ({D} : ℝ) * ({abstract_residual(1)}) := by ring

/-- Explicit exact SOS inequality for oriented law {index}. -/
theorem gram{index:03} (a : Fin 16 → ℝ) :
    0 ≤ {residual(cert)} := by
  have h := fast_certificate_nonneg gramTarget{index:03} gramSquares{index:03}
    gramIdentity{index:03} gramPositive{index:03} a
  have ht : 0 ≤ {cast_target} := h
  have hi : 0 ≤ {real_target} := by simpa only [Int.cast_ofNat, Int.cast_neg] using ht
  have hs := gramScale{index:03} ({sqsum}) {defect} {' '.join(mons)}
  rw [hs] at hi
  exact nonneg_of_mul_nonneg_right hi (by positivity : (0 : ℝ) < {D})
end FourRow
'''
 p=ROOT/'FourRow'/'Grams'/f'G{index:03d}.lean'
 write_lean(p,source)
 return len(source)
if __name__=='__main__':
 import argparse
 a=argparse.ArgumentParser();a.add_argument('--limit',type=int,default=1);args=a.parse_args()
 certs=json.loads((ROOT/'evidence/certificates.json').read_text())['certificates']
 print('generated bytes',sum(emit(i,c) for i,c in enumerate(certs[:args.limit])))
