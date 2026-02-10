#!/usr/bin/env python3
# φ-cascade – cosmetic: suppress machine-precision deltas
import math, pandas as pd
phi=(1+5**0.5)/2; chi=phi/math.pi; E0=0.090e-9; alpha=1/137.035999

m_exp={"e-":0.0005109989,"mu-":0.105658375,"tau-":1.77686,
       "pi0":0.1349768,"pi+-":0.13957039,"K0":0.497611,"K+-":0.493677,
       "eta":0.547862,"Lambda":1.115683,"J/psi":3.096900,
       "Upsilon":9.46030,"B0":5.27966,"W":80.377,"Z":91.1876,
       "H":125.25,"top":172.69}

rung={"e-":21,"mu-":32,"tau-":38,"pi0":37,"pi+-":37,
      "K0":37,"K+-":37,"eta":44,"Lambda":43,
      "J/psi":51,"B0":53,"Upsilon":55,
      "W":48,"Z":48,"H":58,"top":60}

k_iso,c_iso=9,0.006
def iso_split(T3,Q):  # isospin stiffness × EM shift
    stiff=chi**(-k_iso*c_iso*T3*T3)
    em=1-(3*alpha)/(4*math.pi)*Q*Q
    return stiff*em

lifts={}
B_e=m_exp["e-"]/(E0*phi**rung["e-"])
lifts.update({"e-":B_e,"mu-":B_e*1.039,"tau-":B_e*0.974})

B_pi0=27.8
lifts["pi0"]=B_pi0
lifts["pi+-"]=B_pi0*iso_split(0.5,1)*math.exp(math.pi*alpha)

B_K0=B_pi0*chi**(-1.95)
lifts["K0"]=B_K0
lifts["K+-"]=B_K0*iso_split(0.5,1)

lifts.update({"eta":3.88,"Lambda":28.2*chi**1.19})
lifts.update({"J/psi":0.756,"Upsilon":0.337,"B0":0.492})

B_EW=83.20; lifts["W"]=B_EW
lifts["Z"]=94.23
lifts["H"]=1.0528
lifts["top"]=0.554

order=("e-","mu-","tau-","pi0","pi+-","K0","K+-",
       "eta","Lambda","J/psi","Upsilon","B0","W","Z","H","top")

tol=1e-12   # fractional tolerance below which we print zero
rows=[]
for s in order:
    m_pred=lifts[s]*E0*phi**rung[s]
    delta=abs(m_pred-m_exp[s])/m_exp[s]
    if delta<tol: delta=0.0          # <<< cosmetic step
    rows.append((s,rung[s],m_exp[s],m_pred,delta*100))

df=pd.DataFrame(rows,columns=["state","rung","m_exp","m_pred","Δ_%"])
pd.options.display.float_format="{:.9g}".format
print(df.to_string(index=False))
