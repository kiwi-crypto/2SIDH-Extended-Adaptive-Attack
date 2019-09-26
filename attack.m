/*!
 * Recover one bit of the secret.
 */
recover_bit := function(n, jo, ordering, K1, K2, A, pQ)
	H := Oracle(P - K1*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
	for cQ in pQ do
		for j in TwoNeighbours(jInvariant(LongIsogeny(A + (K2-K1)*cQ, 2^n))) do
			if H eq positional_hash(jo, j : order:=ordering) then
				// If we find a hash match, we know the bit is 0
				return 0;
			end if;
	 	end for;
	end for;
	// If there were no matches, the bit is 1
	return 1;
end function;

/*!
 * Test preimage.
 */
test_pimg_bit := function(n, jo1, jo2, K1, K2, pA1, pQ1, pA2, pQ2)
	// Empty lists to store the "good" A and Q candidates
	A1good := [];
	Q1good := [];
	A2good := [];
	Q2good := [];

	if ((K2-K1) mod 2) eq 0 then
		H := Oracle(P - (K1-1)*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
		for cpA1 in pA1 do for cpQ1 in pQ1 do
			j1 := jInvariant(LongIsogeny(cpA1 + 1*cpQ1, 2^n));
			for cpA2 in pA2 do for cpQ2 in pQ2 do
					if H eq positional_hash(j1, jInvariant(LongIsogeny(cpA2 + (K2-K1+1)*cpQ2, 2^n))) then;
						Append(~A1good, cpA1);
						Append(~Q1good, cpQ1);
						Append(~A2good, cpA2);
						Append(~Q2good, cpQ2);
					end if;
			end for; end for;
		end for; end for;
	else
		H := Oracle(P - K2*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
		for cpA1 in pA1 do for cpQ1 in pQ1 do
			if H eq positional_hash(jInvariant(LongIsogeny(cpA1 + (K1-K2)*cpQ1, 2^n)), jo2) then
				Append(~A1good, cpA1);
				Append(~Q1good, cpQ1);
			end if;
		end for; end for;

		H := Oracle(P - K1*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
		for cpA2 in pA2 do for cpQ2 in pQ2 do
			if H eq positional_hash(jo1, jInvariant(LongIsogeny(cpA2 + (K2-K1)*cpQ2, 2^n))) then
				Append(~A2good, cpA2);
				Append(~Q2good, cpQ2);
			end if;
		end for; end for;
	end if;

	// Now we select the first "good" A and its corresponding Q candidates, to keep the loops constant in the next step
	A1ToKeep := A1good[1];
	Q1good_ret := {@@}; // use a set to avoid duplicates
	for ind in [1..#A1good] do
		if A1good[ind] eq A1ToKeep then
			Include(~Q1good_ret, Q1good[ind]);
		end if;
	end for;

	A2ToKeep := A2good[1];
	Q2good_ret := {@@}; // use a set to avoid duplicates
	for ind in [1..#A2good] do
		if A2good[ind] eq A2ToKeep then
			Include(~Q2good_ret, Q2good[ind]);
		end if;
	end for;

	return < A1ToKeep, Setseq(Q1good_ret)>, <A2ToKeep, Setseq(Q2good_ret) >;
end function;

/*!
 * Recover candidates.
 */
make_candies := function(n, a1, a2, CandidateList1, CandidateList2)

	// Split the tuples for readability
	A1 := CandidateList1[1];
	A2 := CandidateList2[1];
	lstQ1 := CandidateList1[2];
	lstQ2 := CandidateList2[2];

	// Setup current Ks.
	K1 := pListToDec(a1, 2);
	K2 := pListToDec(a2, 2);

	// Halve the Qs.
	divQ1 := &cat[DivisionPoints(cQ1, 2) : cQ1 in lstQ1];
	divQ2 := &cat[DivisionPoints(cQ2, 2) : cQ2 in lstQ2];

	// Print the number of Q's to ensure we are not blowing up
	"count Q/divQ", #lstQ1, #lstQ2, #divQ1, #divQ2;

	if ((K2-K1) mod 2) eq 0 then
		H := Oracle(P - K1*(2^(eA-n))*Q, (1+2^(eA-n))*Q, 2^eA);
		// We can just use divQX[1] because any point of correct order will work
		j1_1 := jInvariant(LongIsogeny(A1 + 2^(n-1)*divQ1[1], 2^(n-1)));
		j2_0 := jInvariant(LongIsogeny(A2 + (K2-K1)*divQ2[1], 2^(n-1)));
		j2_1 := jInvariant(LongIsogeny(A2 + (K2-K1)*divQ2[1] + 2^(n-1)*divQ2[1], 2^(n-1)));

		if H eq positional_hash(jE1_0, j2_0) then
			Append( ~a1, 0 );
			Append( ~a2, 0 );
		elif H eq positional_hash(jE1_0, j2_1) then
			Append( ~a1, 0 );
			Append( ~a2, 1 );
		elif H eq positional_hash(j1_1,  j2_0) then
			Append( ~a1, 1 );
			Append( ~a2, 0 );
		elif H eq positional_hash(j1_1,  j2_1) then
			Append( ~a1, 1 );
			Append( ~a2, 1 );
		else
			"Something went wrong";
		end if;

	else
		Append(~a2, recover_bit(n, jE2_0, 2, K2, K1, A1, divQ1));
		Append(~a1, recover_bit(n, jE1_0, 1, K1, K2, A2, divQ2));
	end if;

	pK1 := pListToDec(a1, 2);
	pK2 := pListToDec(a2, 2);

	// Setup phase 2 for branch 1.
	phi1 := deg2_isogeny_from_dual_ker(2^(n-2)*lstQ1[1]);
	pA1 := Preimage(phi1, A1);
	pQ1 := &cat[ Preimage(phi1, cdivQ1) : cdivQ1 in divQ1 ];

	// Setup phase 2 for branch 2.
	phi2 := deg2_isogeny_from_dual_ker(2^(n-2)*lstQ2[1]);
	pA2 := Preimage(phi2, A2);
	pQ2 := &cat[ Preimage(phi2, cdivQ2) : cdivQ2 in divQ2 ];

	// Phase 2 for both branches
	CandidateList1, CandidateList2 := test_pimg_bit(n, jE1_0, jE2_0, pK1, pK2, pA1, pQ1, pA2, pQ2);

	return a1, a2, CandidateList1, CandidateList2;
end function;

// Walk backwards and recover every bit and one suitable set of candidates along the way.
for n in [2..eA] do
	a1, a2; // Print out current bits recovered for debugging.
	"Finding bit", n, "... Time elapsed:", Realtime(start_time);
	a1, a2, CandidateList1, CandidateList2 := make_candies(n, a1, a2, CandidateList1, CandidateList2);
end for;

//This should be it once we reach here.
"Recovered secrets:", pListToDec(a1, 2), pListToDec(a2, 2);
