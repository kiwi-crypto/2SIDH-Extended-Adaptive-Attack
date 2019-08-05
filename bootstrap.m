// Recovered secret bits
a1 := [];
a2 := [];

H := Oracle(P, Q + (2^(eA-1))*Q, 2^eA);
cj1 := -1;
cj2 := -1;

// Get lists of neighbours which are two 2-isogenies away in the graph
j1s := FourNeighbours(jE1_0);
j2s := FourNeighbours(jE2_0);

if H eq positional_hash(jE1_0, jE2_0) then
	Append(~a1, 0);
	Append(~a2, 0);
end if;

// Search for E1'
for j1 in j1s do
	if H eq positional_hash(j1, jE2_0) then
		Append(~a1, 1);
		Append(~a2, 0);
		cj1 := j1;
		break;
	end if;
end for;

// Search for E2'
for j2 in j2s do
	if H eq positional_hash(jE1_0, j2) then
		Append(~a1, 0);
		Append(~a2, 1);
		cj2 := j2;
		break;
	end if;
end for;

// Search for E1' and E2'
for j1 in j1s do
	for j2 in j2s do
		if H eq positional_hash(j1, j2) then
			Append(~a1, 1);
			Append(~a2, 1);
			cj1 := j1;
			cj2 := j2;
			break;
		end if;
	end for;
end for;

//Recover intermediate curves, now we have E1' and/or E2'
if (a1 cat a2) eq [0,0] then
	H := Oracle(P + (2^(eA-1))*Q, Q + (2^(eA-1))*Q, 2^eA);
	for j1 in j1s do
		for j2 in j2s do
			if H eq positional_hash(j1, j2) then
				cj1 := j1;
				cj2 := j2;
				break j1;
			end if;
		end for;
	end for;

	jE1_1 := GetCommonNeighbour(jE1_0, cj1, 1);
	jE2_1 := GetCommonNeighbour(jE2_0, cj2, 1);
elif (a1 cat a2) eq [0,1] then
	H := Oracle(P + (2^(eA-1))*Q, Q + (2^(eA-1))*Q, 2^eA);
	for j1 in j1s do
		if H eq positional_hash(j1, jE2_0) then
			cj1 := j1;
			break;
		end if;
	end for;

	jE1_1 := GetCommonNeighbour(jE1_0, cj1, 1);
	jE2_1 := GetCommonNeighbour(jE2_0, cj2, 1);
elif (a1 cat a2) eq [1,0] then
	H := Oracle(P + (2^(eA-1))*Q, Q + (2^(eA-1))*Q, 2^eA);
	for j2 in j2s do
		if H eq positional_hash(jE1_0, j2) then
			cj2 := j2;
			break;
		end if;
	end for;

	jE1_1 := GetCommonNeighbour(jE1_0, cj1, 1);
	jE2_1 := GetCommonNeighbour(jE2_0, cj2, 1);
elif (a1 cat a2) eq [1,1] then
	jE1_1 := GetCommonNeighbour(jE1_0, cj1, 1);
	jE2_1 := GetCommonNeighbour(jE2_0, cj2, 1);
end if;

//Recover kernels and isogenies.
//ker(phi^i_1) and ker(phi^i_2)
//Note that psi^i_1(A^i) = kerphi^i_1 and psi^i_1(2A^i) = kerphi^i_2
A1 := GetConnectingKernels(GetSSRepFromjInv(jE1_1), jE1_0);
A2 := GetConnectingKernels(GetSSRepFromjInv(jE2_1), jE2_0);

// Adding two different points of order 2 will give the third point of order 2, which is the kernel of the dual E_1 --> E_2
lstQ1 := [ GetConnectingKernels(GetSSRepFromjInv(jE1_1), cj1) + GetConnectingKernels(GetSSRepFromjInv(jE1_1), jE1_0) ];
lstQ2 := [ GetConnectingKernels(GetSSRepFromjInv(jE2_1), cj2) + GetConnectingKernels(GetSSRepFromjInv(jE2_1), jE2_0) ];

CandidateList1 := <A1, lstQ1>;
CandidateList2 := <A2, lstQ2>;

"Bootstrapping complete";
