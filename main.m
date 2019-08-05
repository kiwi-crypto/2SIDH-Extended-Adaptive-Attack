load "library.m";
SetColumns(0);

//AliceSecrets := [ 45, 50 ];
//AliceSecrets := [ 437, 942 ];
//AliceSecrets := [ 436, 942 ];
//AliceSecrets := [ 29206443, 2784946 ];
//AliceSecrets := [ 14897709, 16830519 ];
//AliceSecrets := [ 14897709, 16830541 ];
//AliceSecrets := [ 29206451+4, 2784947 ];
AliceSecrets := [ RandomBits(25), RandomBits(25) ];
"Starting attack with randomly generated secrets:", AliceSecrets;

/*
* Parameters.
*/
p := 24554940634497023;
K := GF(p^2);
_<x> := PolynomialRing(K);

E := EllipticCurve([ 7227205329032435*K.1 + 15319231758733382, 1613665374322417*K.1 + 13936835279929152 ]);

PA := E![ 20746884927937558*K.1 + 10366606564223489, 2983063898332369*K.1 + 347565651777734 ];
QA := E![ 23304177781423091*K.1 + 15534658969717044, 3911681224067712*K.1 + 2003638603203939 ];
PB := E![ 16339026551876410*K.1 + 7944249485412187, 13601096240661708*K.1 + 20561857423119867 ];
QB := E![ 23433067763028489*K.1 + 803842936998551, 4886333153359413*K.1 + 7470641555206833 ];

// Number of bits
eA := Maximum(Ceiling(Log(2, AliceSecrets[1])), Ceiling(Log(2, AliceSecrets[2])));

ord := Factorisation(p+1)[1,2];

if eA gt ord then
	"Secrets are too large";
	exit;
end if;

P := 2^(ord-eA)*PA;
Q := 2^(ord-eA)*QA;

_A1 := P+AliceSecrets[1]*Q;
_A2 := P+AliceSecrets[2]*Q;

E1_0, psi1 := LongIsogeny(_A1, 2^eA);
E2_0, psi2 := LongIsogeny(_A2, 2^eA);
jE1_0 := jInvariant(E1_0);
jE2_0 := jInvariant(E2_0);

/*!
* The ORACLE.
*/
Oracle := function(R, S, ordR : a := AliceSecrets)
	E1, _ := LongIsogeny(R + a[1]*S, ordR);
	E2, _ := LongIsogeny(R + a[2]*S, ordR);
	return positional_hash(jInvariant(E1), jInvariant(E2));
end function;

// clear the secrets to prove that they are not used in the attack
AliceSecrets := [];
_A1 := 0;
_A2 := 0;
psi1 := 0;
psi2 := 0;

start_time := Realtime();

load "bootstrap.m";
load "attack.m";

"Total time elapsed:", Realtime(start_time);