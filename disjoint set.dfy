class DS
{
	var parent: imap<int, int>
	var size: imap<int, nat>
	ghost var maxsize: nat
	ghost var pathnew: seq<int>
	ghost var prevpar: imap<int, int>
	ghost var gx: int
	ghost var gy: int

	ghost function root(x: int, P: imap<int, int>, S: imap<int, nat>, ms: nat): int
		decreases ms - S[x]
		requires x in P
		requires P.Keys == S.Keys
		requires P.Values <= P.Keys
		requires forall a :: a in S ==> ms >= S[a]
		requires forall a :: ((a in S && P[a] != a) ==> S[a] < S[P[a]])
	{
		if P[x] == x then x
		else root(P[x], P, S, ms)
	}

	ghost predicate path(x: int, p: seq<int>, P: imap<int, int>)
	{
		|p| > 0 && 
		x == p[0] && 
		(forall a :: (0 <= a < |p| - 1 ==> (p[a] in P && P[p[a]] == p[a + 1] && p[a] != p[a + 1]))) && 
		p[|p| - 1] in P && P[p[|p| - 1]] == p[|p| - 1]
	}
	
	method MakeSet(x: int)
		modifies this
		requires parent.Keys == size.Keys
		requires parent.Values <= parent.Keys
		ensures x in parent
		ensures parent.Keys == size.Keys
		ensures x in old(parent) ==> unchanged(this)
		ensures x !in old(parent) ==> (parent[x] == x && size[x] == 1 && maxsize == old(maxsize) + 1)
		ensures x !in old(parent) ==> (forall a :: a in parent <==> (a in old(parent) || a == x))
		ensures x !in old(parent) ==> (forall a :: a in size <==> (a in old(size) || a == x))
		ensures x !in old(parent) ==> (forall a :: a in old(parent) ==> old(parent)[a] == parent[a])
		ensures x !in old(parent) ==> (forall a :: a in old(size) ==> old(size)[a] == size[a])
	{
		if x !in parent
		{ 
			parent := parent[x := x];
			size := size[x := 1];
			maxsize := maxsize + 1;
		}
	}

	method Find(x: int) returns (y: int)
		modifies this
		requires x in parent
		requires parent.Keys == size.Keys
		requires parent.Values <= parent.Keys
		requires forall a :: a in size ==> maxsize >= size[a]
		requires forall a :: a in size ==> size[a] > 0
		requires forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
		ensures parent.Keys == size.Keys
		ensures parent.Values <= parent.Keys
		ensures forall a :: a in size ==> maxsize >= size[a]
		ensures forall a :: a in size ==> size[a] > 0
		ensures forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
		ensures old(size) == size
		ensures old(parent).Keys == parent.Keys
		ensures old(maxsize) == maxsize
		ensures path(x, pathnew, parent)
		ensures pathnew[|pathnew| - 1] == y
		ensures forall a :: 0 <= a < |pathnew| ==> pathnew[a] in parent
		ensures forall a :: 0 <= a < |pathnew| - 1 ==> old(parent)[old(parent)[pathnew[a]]] == pathnew[a + 1]
		ensures forall a :: (a in parent && a !in pathnew) ==> old(parent)[a] == parent[a]
		ensures forall a :: a in parent ==> (old(parent)[a] == a <==> parent[a] == a)
		ensures forall a :: a in pathnew ==> y == root(a, old(parent), old(size), old(maxsize))
	{
		pathnew := [];
		var z: int := x;

		while z != parent[z]
			decreases maxsize - size[z]
			invariant old(size) == size
			invariant old(maxsize) == maxsize
			invariant z in parent.Keys
			invariant parent.Keys == size.Keys
			invariant parent.Values <= parent.Keys
			invariant forall a :: a in size ==> maxsize >= size[a]
			invariant forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
			invariant forall a :: 0 <= a < |pathnew| ==> pathnew[a] in parent
			invariant |pathnew| > 0 ==> old(parent)[old(parent)[pathnew[|pathnew| - 1]]] == z
			invariant |pathnew| > 0 ==> parent[pathnew[|pathnew| - 1]] == z
			invariant forall a :: 0 <= a < |pathnew| - 1 ==> old(parent)[old(parent)[pathnew[a]]] == pathnew[a + 1]
			invariant forall a :: 0 <= a < |pathnew| - 1 ==> pathnew[a] != pathnew[a + 1]
			invariant forall a :: 0 <= a < |pathnew| - 1 ==> parent[pathnew[a]] == pathnew[a + 1]
			invariant forall a :: 0 <= a < |pathnew| ==> old(size)[pathnew[a]] < old(size)[z]
			invariant |pathnew| > 0 ==> pathnew[0] == x
			invariant |pathnew| == 0 ==> x == z
			invariant forall a :: (a in parent && a !in pathnew) ==> old(parent)[a] == parent[a]
			invariant forall a :: (a in parent ==> (old(parent)[a] == a <==> parent[a] == a))
			invariant forall a :: a in pathnew ==> root(a, old(parent), old(size), old(maxsize)) == root(z, old(parent), old(size), old(maxsize))
		{
			pathnew := pathnew + [z];
			parent := parent[z := parent[parent[z]]];
			z := parent[z];
		}

		pathnew := pathnew + [z];
		return z;
	}

	method Union(x: int, y: int)
		modifies this
		requires parent.Keys == size.Keys
		requires parent.Values <= parent.Keys
		requires forall a :: a in size ==> maxsize >= size[a]
		requires forall a :: a in size ==> size[a] > 0
		requires forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
		ensures parent.Keys == size.Keys
		ensures parent.Values <= parent.Keys
		ensures forall a :: a in size ==> size[a] > 0
		ensures forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
		ensures old(size).Keys == size.Keys
		ensures old(parent).Keys == parent.Keys
		ensures old(maxsize) == maxsize
		ensures (x !in parent || y !in parent) ==> unchanged(this)
		ensures (x in parent && y in parent) ==> gx in size
		ensures (x in parent && y in parent) ==> gy in size
		ensures (x in parent && y in parent) ==> forall a :: (a in parent ==> (old(parent)[a] == a <==> (parent[a] == a || a == gx || a == gy)))
		ensures (x in parent && y in parent && gx == gy) ==> (prevpar == parent && old(size) == size)
		ensures (x in parent && y in parent && gx != gy) ==> prevpar.Keys == parent.Keys
		ensures (x in parent && y in parent && gx != gy && size[gx] < size[gy]) ==> (parent[gy] == gy && gy == parent[gx] != gx && size[gy] == old(size)[gx] + old(size)[gy])
		ensures (x in parent && y in parent && gx != gy && size[gx] < size[gy]) ==> forall a :: (a in size && a != gy ==> size[a] == old(size)[a])
		ensures (x in parent && y in parent && gx != gy && size[gx] < size[gy]) ==> prevpar[gx] == gx
		ensures (x in parent && y in parent && gx != gy && size[gx] < size[gy]) ==> parent[gx] == gy
		ensures (x in parent && y in parent && gx != gy && size[gx] < size[gy]) ==> forall a :: (a in prevpar && a != gx ==> prevpar[a] == parent[a])
		ensures (x in parent && y in parent && gx != gy && size[gx] >= size[gy]) ==> (parent[gx] == gx && gx == parent[gy] != gy && size[gx] == old(size)[gx] + old(size)[gy])
		ensures (x in parent && y in parent && gx != gy && size[gx] >= size[gy]) ==> forall a :: (a in size && a != gx ==> size[a] == old(size)[a])
		ensures (x in parent && y in parent && gx != gy && size[gx] >= size[gy]) ==> prevpar[gy] == gy
		ensures (x in parent && y in parent && gx != gy && size[gx] >= size[gy]) ==> parent[gy] == gx
		ensures (x in parent && y in parent && gx != gy && size[gx] >= size[gy]) ==> forall a :: (a in prevpar && a != gy ==> prevpar[a] == parent[a])
	{
		if x in parent && y in parent
		{
			var x': int := Find(x);
			var y': int := Find(y);
			prevpar := parent;
			gx := x';
			gy := y';

			if x' != y'
			{
				if size[x'] < size[y']
				{
					parent := parent[x' := y'];
					size := size[y' := size[x'] + size[y']];
				}
				else
				{
					parent := parent[y' := x'];
					size := size[x' := size[x'] + size[y']];
				}
			}

			assert gx == x';
			assert gy == y';
		}
	}

	constructor ()
		ensures maxsize == 0
		ensures parent.Keys == size.Keys
		ensures parent.Values <= parent.Keys
		ensures forall a :: a in size ==> maxsize >= size[a]
		ensures forall a :: a in size ==> size[a] > 0
		ensures forall a :: ((a in size && parent[a] != a) ==> size[a] < size[parent[a]])
		ensures forall a :: a !in parent
		ensures forall a :: a !in size
		ensures maxsize == 0
	{
		parent := imap[];
		size := imap[];
		maxsize := 0;
	}
}