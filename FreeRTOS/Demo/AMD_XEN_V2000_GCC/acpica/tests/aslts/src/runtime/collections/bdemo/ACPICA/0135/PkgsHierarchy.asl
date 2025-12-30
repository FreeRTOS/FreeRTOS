/*
 * Some or all of this work - Copyright (c) 2006 - 2021, Intel Corp.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without modification,
 * are permitted provided that the following conditions are met:
 *
 * Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 * Neither the name of Intel Corporation nor the names of its contributors
 * may be used to endorse or promote products derived from this software
 * without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
 * LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
 * NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,
 * EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Hierarchy of Packages
 *
 * It is a 4-level (not including the root Package-node) hierarchy
 * of Packages. Each package (pkg-node), including the root Package,
 * has 4 Packages which (not including Package-nodes of the last
 * 3-th level) in turn has 4 children.
 * Generate and put into each pkg-node references to all other
 * pkg-nodes. Then go round all the pkg-nodes and verify read-access
 * through all the references packed into each of those nodes.
 *
 * 0x22 Outstanding allocations because of
 * AcpiExec doesn't run the unload of the table have been processed.
 * All they are caused by call to SRMT Method.
 *
 * Outstanding: 0x22 allocations after execution.
 *
 * chn0 - set it to either 1 or 2:
 * Name(chn0, 1)	// number of children of pkg-node to be actually processed (1,2,3,4)
 */

/*
 * Bit-maps of operations
 */
Name(OP00, 0x01)		// read and verify Integer-IDs
Name(OP01, 0x02)		// re-write Integer-IDs
Name(OP02, 0x04)		// re-write the whole pkg-nodes
Name(OP03, 0x08)		// re-write references
Name(OPFF, 0x0F)		// mask of opcode of operation
Name(OP10, 0x0f0000)	// type of current (read) Integer-IDs
Name(OP11, 0x0f00000)	// type of new (re-write) Integer-IDs

/*
 * Generate references to arg2-number elements of all pkg-nodes
 * of arg0 and pack up them per-level into arg1.
 *
 * arg0 - reference to (Package,pHR0), IRefs to arg2 elements of Pkg-nodes of pHR0
 * arg1 - (Package,pIRx), are to be stored into elements of pIRx (from 0).
 * arg2 - number of children of pkg-node to be actually processed
 * arg3 - index of elements of pkg-nodes of arg0 to be pointed to by ref
 */
Method(mfdd, 4, Serialized)
{
	Name(ind0, 0)	// cur index of element of arg1-Package where to store ref
	Name(ind1, 0)
	Name(ind2, 0)
	Name(ind3, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(lpN1, 0)
	Name(lpC1, 0)
	Name(lpN2, 0)
	Name(lpC2, 0)
	Name(lpN3, 0)
	Name(lpC3, 0)

	Store(arg2, lpN0)
	Store(0, lpC0)
	While (lpN0) {

        Store(Index(DerefOf(arg0), lpC0), Index(DerefOf(Index(arg1, 0)), ind0))

        Store(arg2, lpN1)
        Store(0, lpC1)
        While (lpN1) {

          Store(Index(DerefOf(Index(DerefOf(arg0), lpC0)), lpC1), Index(DerefOf(Index(arg1, 1)), ind1))

          Store(arg2, lpN2)
          Store(0, lpC2)
          While (lpN2) {

            Store(Index(DerefOf(Index(DerefOf(Index(DerefOf(arg0), lpC0)), lpC1)), lpC2), Index(DerefOf(Index(arg1, 2)), ind2))

            Store(arg2, lpN3)
            Store(0, lpC3)
            While (lpN3) {

              Store(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(arg0), lpC0)), lpC1)), lpC2)), lpC3), Index(DerefOf(Index(arg1, 3)), ind3))

              Increment(ind3)
              Decrement(lpN3)
              Increment(lpC3)
            }
            Increment(ind2)
            Decrement(lpN2)
            Increment(lpC2)
          }
          Increment(ind1)
          Decrement(lpN1)
          Increment(lpC1)
        }
        Increment(ind0)
        Decrement(lpN0)
        Increment(lpC0)
	}
}

/*
 * Put reference arg3 into arg2-th elements of all Pkg-nodes of pHR0 Package
 *
 * arg0 - reference to Package,pHR0
 * arg1 - number of children of pkg-node to be actually processed
 * arg2 - index in arg0-pkg-nodes where to store reference
 * arg3 - reference
 */
Method(mfde, 4, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(lpN1, 0)
	Name(lpC1, 0)
	Name(lpN2, 0)
	Name(lpC2, 0)
	Name(lpN3, 0)
	Name(lpC3, 0)


	Store(arg1, lpN0)
	Store(0, lpC0)
	While (lpN0) {

        Index(DerefOf(arg0), lpC0, Local0)
        Store(arg3, Index(DerefOf(Local0), arg2))

        Store(arg1, lpN1)
        Store(0, lpC1)
        While (lpN1) {

          Index(DerefOf(arg0), lpC0, Local0)
          Store(arg3, Index(DerefOf(Index(DerefOf(Local0), lpC1)), arg2))

          Store(arg1, lpN2)
          Store(0, lpC2)
          While (lpN2) {

            Index(DerefOf(arg0), lpC0, Local0)
            Store(arg3, Index(DerefOf(Index(DerefOf(Index(DerefOf(Local0), lpC1)), lpC2)), arg2))

            Store(arg1, lpN3)
            Store(0, lpC3)
            While (lpN3) {

              Index(DerefOf(arg0), lpC0, Local0)
              Store(arg3, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Local0), lpC1)), lpC2)), lpC3)), arg2))

              Decrement(lpN3)
              Increment(lpC3)
            }
            Decrement(lpN2)
            Increment(lpC2)
          }
          Decrement(lpN1)
          Increment(lpC1)
        }
        Decrement(lpN0)
        Increment(lpC0)
	}
}

/*
 * Put elements of package arg0 (references) into elements of arg1
 *
 * arg0 - pIRx-Package (references)
 * arg1 - reference to pHRx-Package (hierarchy) - where to put references
 * arg2 - number of children of pkg-node to be actually processed
 * arg3 - start index in arg1 where to store references
 */
Method(mfdf, 4, Serialized)
{
	Name(ind0, 0)
	Name(num, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)

	Name(pp00, Package(1) {})
	Name(pp01, Package(1) {})


	Store(arg2, num)

	/* Level 0 */

	Store(Index(arg0, 0), Local0)
	Store(DerefOf(Local0), pp00)

	Store(arg3, ind0)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(pp00, lpC0, Local0)
		Store(DerefOf(Local0), Local1)

		mfde(arg1, arg2, ind0, Local1)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 1 */

	Store(Index(arg0, 1), Local0)
	Store(DerefOf(Local0), pp00)

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(pp00, lpC0, Local0)
		Store(DerefOf(Local0), Local1)

		mfde(arg1, arg2, ind0, Local1)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 2 */

	Store(Index(arg0, 2), Local0)
	Store(DerefOf(Local0), pp00)

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(pp00, lpC0, Local0)
		Store(DerefOf(Local0), Local1)

		mfde(arg1, arg2, ind0, Local1)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 3 */

	Store(Index(arg0, 3), Local0)
	Store(DerefOf(Local0), pp00)

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(pp00, lpC0, Local0)
		Store(DerefOf(Local0), Local1)

		mfde(arg1, arg2, ind0, Local1)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}
}

/*
 * Generate the benchmark value of Integer-ID and
 * verify by it the actual value of Integer-ID.
 *
 * arg0 - coefficient of maximal hierarchy of Packages
 * arg1 - number of children of pkg-node to be actually processed
 * arg2 - level + index inside level of source pkg-node
 * arg3 - level + index inside level of target pkg-node
 * arg4 - the value of Integer-ID
 * arg5 - bit-map of operations
 */
Method(mfe2, 6, Serialized)
{
	/* Index */

	Name(lpN0, 0)
	Name(lpC0, 0)

	Name(lls0, 0)	// level of source pkg-node
	Name(ins0, 0)	// index inside level of source pkg-node
	Name(llt0, 0)	// level of target pkg-node
	Name(int0, 0)	// index inside level of target pkg-node

	Store(0, Local7)

	And(arg2, 0x0ffff, ins0)
	ShiftRight(arg2, 16, Local0)
	And(Local0, 0x0ffff, lls0)

	And(arg3, 0x0ffff, int0)
	ShiftRight(arg3, 16, Local0)
	And(Local0, 0x0ffff, llt0)

	And(int0, 0x0ffff, Local2)

	if (llt0) {

		/*
		 * ASSUMPTION: 256 on 3-th level is maximum
		 * for this model of packages
		 */
		Divide(Local2, 8, Local0, Local1)
		Multiply(Local1, 64, Local5)

		Divide(Local0, 4, Local0, Local1)
		Multiply(Local1, 16, Local6)
		Add(Local5, Local6, Local5)

		Divide(Local0, 2, Local0, Local1)
		Multiply(Local1, 4, Local6)
		Add(Local5, Local6, Local5)

		Add(Local5, Local0, Local5)
	} else {
		Store(Local2, Local5)
	}

	Or(0xab000000, Local5, Local3)

	/* Level */

	And(llt0, 0x0f, Local0)
	ShiftLeft(Local0, 16, Local1)
	Or(Local1, Local3, Local0)

	Store(mfe3(Local0, arg5, 0), Local1)

	if (LNotEqual(arg4, Local1)) {
		Store(1, Local7)
		err("", zFFF, __LINE__, 0, 0, arg4, Local1)
		Store("================= Params:", debug)
		Store(arg0, Debug)
		Store(arg1, Debug)
		Store(arg2, Debug)
		Store(arg3, Debug)
		Store(arg4, Debug)
		Store(arg5, Debug)
		Store(lls0, Debug)
		Store(ins0, Debug)
		Store(llt0, Debug)
		Store(int0, Debug)
		Store("=================.", debug)
	}

	return (Local7)
}

/*
 * Modify Integer-ID
 *
 * arg0 - the value of Integer-ID
 * arg1 - bit-map of operations
 * arg2 - 0 - for read, 1 - for re-write
 */
Method(mfe3, 3)
{
	And(arg0, 0xff0fffff, Local0)
	if (arg2) {
		And(arg1, OP11, Local1)
	} else {
		And(arg1, OP10, Local2)
		ShiftLeft(Local2, 4, Local1)
	}
	Or(Local0, Local1, Local7)

	return (Local7)
}

/*
 * Verify the value of Integer-ID of pkg-node
 *
 * arg0 - pkg-node Package of pHRx-Package
 * arg1 - coefficient of maximal hierarchy of Packages
 * arg2 - number of children of pkg-node to be actually processed
 * arg3 - start index of location of references in pkg-nodes
 * arg4 - level of arg0 + index inside level of arg0
 * arg5 - bit-map of operations
 * arg6 - index of Integer-ID in pkg-nodes
 */
Method(mfe0, 7, Serialized)
{
	Name(ind0, 0)
	Name(num, 0)

	Name(lpN0, 0)
	Name(lpC0, 0)

	Store(arg2, num)

	/* Level 0 */

	Store(arg3, ind0)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(arg0, ind0, Local0)		// IRef to some ref of pkg-node
		Store(DerefOf(Local0), Local1)	// reference
		Store(DerefOf(Local1), Local2)	// another pkg-node referred to
		Store(DerefOf(Index(Local2, arg6)), Local3)	// Integer-ID

		mfe2(arg1, arg2, arg4, lpC0, Local3, arg5)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 1 */

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(arg0, ind0, Local0)
		Store(DerefOf(Local0), Local1)
		Store(DerefOf(Local1), Local2)
		Store(DerefOf(Index(Local2, arg6)), Local3)

		Or(0x10000, lpC0, Local7)

		mfe2(arg1, arg2, arg4, Local7, Local3, arg5)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 2 */

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(arg0, ind0, Local0)
		Store(DerefOf(Local0), Local1)
		Store(DerefOf(Local1), Local2)
		Store(DerefOf(Index(Local2, arg6)), Local3)

		Or(0x20000, lpC0, Local7)

		mfe2(arg1, arg2, arg4, Local7, Local3, arg5)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}

	/* Level 3 */

	Multiply(num, arg2, num)

	Store(num, lpN0)
	Store(0, lpC0)
	While (lpN0) {

		Index(arg0, ind0, Local0)
		Store(DerefOf(Local0), Local1)
		Store(DerefOf(Local1), Local2)
		Store(DerefOf(Index(Local2, arg6)), Local3)

		Or(0x30000, lpC0, Local7)

		mfe2(arg1, arg2, arg4, Local7, Local3, arg5)

		Increment(ind0)
		Decrement(lpN0)
		Increment(lpC0)
	}
}

/*
 * Verify the contents of pHRx-Package (Integer-IDs) by read access
 * through References packed into all pkg-nodes.
 *
 * arg0 - pHRx-Package (hierarchy), fully initialized
 * arg1 - number of children of pkg-node to be actually processed
 * arg2 - start index of location of references in arg0-pkg-nodes
 * arg3 - coefficient of maximal hierarchy of Packages
 * arg4 - bit-map of operations
 * arg5 - index of Integer-ID in pkg-nodes
 */
Method(mfe1, 6, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(lpN1, 0)
	Name(lpC1, 0)
	Name(lpN2, 0)
	Name(lpC2, 0)
	Name(lpN3, 0)
	Name(lpC3, 0)

	Name(pkg0, Package(1) {})
	Name(pkg1, Package(1) {})
	Name(pkg2, Package(1) {})
	Name(pkg3, Package(1) {})

	Store(arg1, lpN0)
	Store(0, lpC0)
	While (lpN0) {

        Index(arg0, lpC0, Local0)
        CopyObject(DerefOf(Local0), pkg0)

        mfe0(pkg0, arg3, arg1, arg2, lpC0, arg4, arg5)
        Store(arg1, lpN1)
        Store(0, lpC1)
        While (lpN1) {

          Index(pkg0, lpC1, Local1)
          CopyObject(DerefOf(Local1), pkg1)
          Or(0x10000, lpC1, Local7)
          mfe0(pkg1, arg3, arg1, arg2, Local7, arg4, arg5)

          Store(arg1, lpN2)
          Store(0, lpC2)
          While (lpN2) {

            Index(pkg1, lpC2, Local2)
            CopyObject(DerefOf(Local2), pkg2)
            Or(0x20000, lpC2, Local7)
            mfe0(pkg2, arg3, arg1, arg2, Local7, arg4, arg5)
            Store(arg1, lpN3)
            Store(0, lpC3)
            While (lpN3) {

              Index(pkg2, lpC3, Local3)
              CopyObject(DerefOf(Local3), pkg3)
              Or(0x30000, lpC3, Local7)
              mfe0(pkg3, arg3, arg1, arg2, Local7, arg4, arg5)

              Decrement(lpN3)
              Increment(lpC3)
            }
            Decrement(lpN2)
            Increment(lpC2)
          }
          Decrement(lpN1)
          Increment(lpC1)
        }
        Decrement(lpN0)
        Increment(lpC0)
	}
}

/*
 * Rewrite Integer-IDs for all pkg-nodes of hierarchy -
 * read previous value generate new and write back to pkg-node.
 *
 * arg0 - reference to Package,pHR0
 * arg1 - number of children of pkg-node to be actually processed
 * arg2 - index of Integer-ID in pkg-nodes
 * arg3 - start index of location of references in pkg-nodes
 * arg4 - bit-map of operations
 */
Method(mfe4, 5, Serialized)
{
	Name(lpN0, 0)
	Name(lpC0, 0)
	Name(lpN1, 0)
	Name(lpC1, 0)
	Name(lpN2, 0)
	Name(lpC2, 0)
	Name(lpN3, 0)
	Name(lpC3, 0)

	Name(lpN4, 0)
	Name(lpC4, 0)

	Name(nds0, 0) // number of pkg-nodes actually processed
	Name(iRF0, 0) // current index of element with reference

	Name(op00, 0)
	Name(wrID, 0)
	Name(wrPK, 0)
	Name(wrRF, 0)

	Name(pkg0, Package(1) {})
	Name(pkg, Package(1) {})

	And(arg4, OPFF, op00)

	Switch (ToInteger (op00)) {
	Case (0x02) {
		/* re-write Integer-IDs */
		Store(1, wrID)
	}
	Case (0x04) {
		/* re-write pkg-nodes */
		Store(1, wrPK)
	}
	Case (0x08) {
		/* re-write references */
		Store(mfe5(arg1), nds0)
		Store(1, wrRF)
	}
	Default {
		return
	}}

      Store(arg1, lpN0)
      Store(0, lpC0)
      While (lpN0) {

        Index(DerefOf(arg0), lpC0, pkg0)	// lpC0-th pkg-node of 0 level

        if (wrID) {
          Store(DerefOf(Index(DerefOf(pkg0), arg2)), Local7) // Integer-ID
          Store(mfe3(Local7, arg4, 1), Local6)
          Store(Local6, Index(DerefOf(pkg0), arg2))
        } elseif (wrRF) {
          Store(nds0, lpN4)
          Store(0, lpC4)
          Store(arg3, iRF0)
          While (lpN4) {
            Store(DerefOf(Index(DerefOf(pkg0), iRF0)), Local7) // reference
            Store(Local7, Index(DerefOf(pkg0), iRF0))
            Increment(iRF0)
            Decrement(lpN4)
            Increment(lpC4)
          }
        }

        Store(arg1, lpN1)
        Store(0, lpC1)
        While (lpN1) {

          if (wrID) {
            Store(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), arg2)), Local7)
            Store(mfe3(Local7, arg4, 1), Local6)
            Store(Local6, Index(DerefOf(Index(DerefOf(pkg0), lpC1)), arg2))
          } elseif (wrRF) {
            Store(nds0, lpN4)
            Store(0, lpC4)
            Store(arg3, iRF0)
            While (lpN4) {
              Store(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), iRF0)), Local7)
              Store(Local7, Index(DerefOf(Index(DerefOf(pkg0), lpC1)), iRF0))
              Store(Local7, Index(DerefOf(Index(DerefOf(pkg0), lpC1)), iRF0))
              Increment(iRF0)
              Decrement(lpN4)
              Increment(lpC4)
            }
          }

          Store(arg1, lpN2)
          Store(0, lpC2)
          While (lpN2) {

            if (wrID) {
              Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), arg2)), Local7)
              Store(mfe3(Local7, arg4, 1), Local6)
              Store(Local6, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), arg2))
            } elseif (wrRF) {
              Store(nds0, lpN4)
              Store(0, lpC4)
              Store(arg3, iRF0)
              While (lpN4) {
                Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), iRF0)), Local7)
                Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), iRF0))
                Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), iRF0))
                Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), iRF0))
                Increment(iRF0)
                Decrement(lpN4)
                Increment(lpC4)
              }
            }

            Store(arg1, lpN3)
            Store(0, lpC3)
            While (lpN3) {

              if (wrID) {
                Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), arg2)), Local7)
                Store(mfe3(Local7, arg4, 1), Local6)
                Store(Local6, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), arg2))
              } elseif (wrPK) {
                Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), pkg)
                if (LEqual(lpC3, 1)) {
                  Store(pkg, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3))
                  Store(pkg, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3))
                  Store(pkg, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3))
                } else {
                  Store(pkg, Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3))
                }
              } elseif (wrRF) {
                Store(nds0, lpN4)
                Store(0, lpC4)
                Store(arg3, iRF0)
                While (lpN4) {
                  Store(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), iRF0)), Local7)
                  Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), iRF0))
                  Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), iRF0))
                  Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), iRF0))
                  Store(Local7, Index(DerefOf(Index(DerefOf(Index(DerefOf(Index(DerefOf(pkg0), lpC1)), lpC2)), lpC3)), iRF0))
                  Increment(iRF0)
                  Decrement(lpN4)
                  Increment(lpC4)
                }
              }

              Decrement(lpN3)
              Increment(lpC3)
            }
            Decrement(lpN2)
            Increment(lpC2)
          }
          Decrement(lpN1)
          Increment(lpC1)
        }
        Decrement(lpN0)
        Increment(lpC0)
	}
}

/*
 * Return number of pkg-nodes actually processed.
 *
 * arg0 - number of children of pkg-node to be actually processed
 */
Method(mfe5, 1)
{
	Store(arg0, Local0)
	Multiply(Local0, arg0, Local1)
	Multiply(Local1, arg0, Local2)
	Multiply(Local2, arg0, Local3)

	Add(Local0, Local1, Local4)
	Add(Local2, Local3, Local5)

	Add(Local4, Local5, Local7)

	return (Local7)
}

/*
 * Static hierarchy of Packages (maximal):
 *
 * 1. Levels: root + 4
 * 2. Pkg-node: 4 children-Packages
 * 3. Integer-ID: reflects level (0-3) and index inside level of pkg-node
 * 4. References: (4+16+64+256) == 340 maximum
 * 5  Total ==   4 (Pkg-nodes)
 *           +   1 (Integer-ID)
 *           + 340 (References to inner nodes)
 *           + 340 (References to nodes of another hierarchy)
 *             ===
 *             685
 */
Method(mfdc,, Serialized)
{
	Name(pr00, 0)

	/*
	 * Coefficient of maximal hierarchy of Packages
	 * represented by this model.
	 */
	Name(HR00, 4)

	Name(iint, 4)	// index of Integer-ID in pkg-nodes
	Name(iirf, 0)	// start index of location of INTERNAL-references in pkg-nodes
	Name(icrf, 345)	// start index of location of CROSS-references in pkg-nodes
	Name(sz, 685)	// full size of Package
	Name(chn0, 1)	// number of children of pkg-node to be actually processed (1,2,3,4)

	/* Package of hierarchy */

	Name(pHR0, Package(sz) {
        Package(sz) {
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030000,
              },
              Package(sz) {0,1,2,3, 0xab030001,
              },
              Package(sz) {0,1,2,3, 0xab030002,
              },
              Package(sz) {0,1,2,3, 0xab030003,
              },
              0xab020000
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030004,
              },
              Package(sz) {0,1,2,3, 0xab030005,
              },
              Package(sz) {0,1,2,3, 0xab030006,
              },
              Package(sz) {0,1,2,3, 0xab030007,
              },
              0xab020001
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030008,
              },
              Package(sz) {0,1,2,3, 0xab030009,
              },
              Package(sz) {0,1,2,3, 0xab03000a,
              },
              Package(sz) {0,1,2,3, 0xab03000b,
              },
              0xab020002
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03000c,
              },
              Package(sz) {0,1,2,3, 0xab03000d,
              },
              Package(sz) {0,1,2,3, 0xab03000e,
              },
              Package(sz) {0,1,2,3, 0xab03000f,
              },
              0xab020003
            },
            0xab010000
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030010,
              },
              Package(sz) {0,1,2,3, 0xab030011,
              },
              Package(sz) {0,1,2,3, 0xab030012,
              },
              Package(sz) {0,1,2,3, 0xab030013,
              },
              0xab020004
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030014,
              },
              Package(sz) {0,1,2,3, 0xab030015,
              },
              Package(sz) {0,1,2,3, 0xab030016,
              },
              Package(sz) {0,1,2,3, 0xab030017,
              },
              0xab020005
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030018,
              },
              Package(sz) {0,1,2,3, 0xab030019,
              },
              Package(sz) {0,1,2,3, 0xab03001a,
              },
              Package(sz) {0,1,2,3, 0xab03001b,
              },
              0xab020006
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03001c,
              },
              Package(sz) {0,1,2,3, 0xab03001d,
              },
              Package(sz) {0,1,2,3, 0xab03001e,
              },
              Package(sz) {0,1,2,3, 0xab03001f,
              },
              0xab020007
            },
            0xab010001
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030020,
              },
              Package(sz) {0,1,2,3, 0xab030021,
              },
              Package(sz) {0,1,2,3, 0xab030022,
              },
              Package(sz) {0,1,2,3, 0xab030023,
              },
              0xab020008
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030024,
              },
              Package(sz) {0,1,2,3, 0xab030025,
              },
              Package(sz) {0,1,2,3, 0xab030026,
              },
              Package(sz) {0,1,2,3, 0xab030027,
              },
              0xab020009
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030028,
              },
              Package(sz) {0,1,2,3, 0xab030029,
              },
              Package(sz) {0,1,2,3, 0xab03002a,
              },
              Package(sz) {0,1,2,3, 0xab03002b,
              },
              0xab02000a
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03002c,
              },
              Package(sz) {0,1,2,3, 0xab03002d,
              },
              Package(sz) {0,1,2,3, 0xab03002e,
              },
              Package(sz) {0,1,2,3, 0xab03002f,
              },
              0xab02000b
            },
            0xab010002
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030030,
              },
              Package(sz) {0,1,2,3, 0xab030031,
              },
              Package(sz) {0,1,2,3, 0xab030032,
              },
              Package(sz) {0,1,2,3, 0xab030033,
              },
              0xab02000c
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030034,
              },
              Package(sz) {0,1,2,3, 0xab030035,
              },
              Package(sz) {0,1,2,3, 0xab030036,
              },
              Package(sz) {0,1,2,3, 0xab030037,
              },
              0xab02000d
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030038,
              },
              Package(sz) {0,1,2,3, 0xab030039,
              },
              Package(sz) {0,1,2,3, 0xab03003a,
              },
              Package(sz) {0,1,2,3, 0xab03003b,
              },
              0xab02000e
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03003c,
              },
              Package(sz) {0,1,2,3, 0xab03003d,
              },
              Package(sz) {0,1,2,3, 0xab03003e,
              },
              Package(sz) {0,1,2,3, 0xab03003f,
              },
              0xab02000f
            },
            0xab010003
          },
          0xab000000
        },
        Package(sz) {
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030040,
              },
              Package(sz) {0,1,2,3, 0xab030041,
              },
              Package(sz) {0,1,2,3, 0xab030042,
              },
              Package(sz) {0,1,2,3, 0xab030043,
              },
              0xab020010
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030044,
              },
              Package(sz) {0,1,2,3, 0xab030045,
              },
              Package(sz) {0,1,2,3, 0xab030046,
              },
              Package(sz) {0,1,2,3, 0xab030047,
              },
              0xab020011
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030048,
              },
              Package(sz) {0,1,2,3, 0xab030049,
              },
              Package(sz) {0,1,2,3, 0xab03004a,
              },
              Package(sz) {0,1,2,3, 0xab03004b,
              },
              0xab020012
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03004c,
              },
              Package(sz) {0,1,2,3, 0xab03004d,
              },
              Package(sz) {0,1,2,3, 0xab03004e,
              },
              Package(sz) {0,1,2,3, 0xab03004f,
              },
              0xab020013
            },
            0xab010004
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030050,
              },
              Package(sz) {0,1,2,3, 0xab030051,
              },
              Package(sz) {0,1,2,3, 0xab030052,
              },
              Package(sz) {0,1,2,3, 0xab030053,
              },
              0xab020014
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030054,
              },
              Package(sz) {0,1,2,3, 0xab030055,
              },
              Package(sz) {0,1,2,3, 0xab030056,
              },
              Package(sz) {0,1,2,3, 0xab030057,
              },
              0xab020015
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030058,
              },
              Package(sz) {0,1,2,3, 0xab030059,
              },
              Package(sz) {0,1,2,3, 0xab03005a,
              },
              Package(sz) {0,1,2,3, 0xab03005b,
              },
              0xab020016
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03005c,
              },
              Package(sz) {0,1,2,3, 0xab03005d,
              },
              Package(sz) {0,1,2,3, 0xab03005e,
              },
              Package(sz) {0,1,2,3, 0xab03005f,
              },
              0xab020017
            },
            0xab010005
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030060,
              },
              Package(sz) {0,1,2,3, 0xab030061,
              },
              Package(sz) {0,1,2,3, 0xab030062,
              },
              Package(sz) {0,1,2,3, 0xab030063,
              },
              0xab020018
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030064,
              },
              Package(sz) {0,1,2,3, 0xab030065,
              },
              Package(sz) {0,1,2,3, 0xab030066,
              },
              Package(sz) {0,1,2,3, 0xab030067,
              },
              0xab020019
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030068,
              },
              Package(sz) {0,1,2,3, 0xab030069,
              },
              Package(sz) {0,1,2,3, 0xab03006a,
              },
              Package(sz) {0,1,2,3, 0xab03006b,
              },
              0xab02001a
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03006c,
              },
              Package(sz) {0,1,2,3, 0xab03006d,
              },
              Package(sz) {0,1,2,3, 0xab03006e,
              },
              Package(sz) {0,1,2,3, 0xab03006f,
              },
              0xab02001b
            },
            0xab010006
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030070,
              },
              Package(sz) {0,1,2,3, 0xab030071,
              },
              Package(sz) {0,1,2,3, 0xab030072,
              },
              Package(sz) {0,1,2,3, 0xab030073,
              },
              0xab02001c
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030074,
              },
              Package(sz) {0,1,2,3, 0xab030075,
              },
              Package(sz) {0,1,2,3, 0xab030076,
              },
              Package(sz) {0,1,2,3, 0xab030077,
              },
              0xab02001d
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030078,
              },
              Package(sz) {0,1,2,3, 0xab030079,
              },
              Package(sz) {0,1,2,3, 0xab03007a,
              },
              Package(sz) {0,1,2,3, 0xab03007b,
              },
              0xab02001e
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03007c,
              },
              Package(sz) {0,1,2,3, 0xab03007d,
              },
              Package(sz) {0,1,2,3, 0xab03007e,
              },
              Package(sz) {0,1,2,3, 0xab03007f,
              },
              0xab02001f
            },
            0xab010007
          },
          0xab000001
        },
        Package(sz) {
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030080,
              },
              Package(sz) {0,1,2,3, 0xab030081,
              },
              Package(sz) {0,1,2,3, 0xab030082,
              },
              Package(sz) {0,1,2,3, 0xab030083,
              },
              0xab020020
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030084,
              },
              Package(sz) {0,1,2,3, 0xab030085,
              },
              Package(sz) {0,1,2,3, 0xab030086,
              },
              Package(sz) {0,1,2,3, 0xab030087,
              },
              0xab020021
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030088,
              },
              Package(sz) {0,1,2,3, 0xab030089,
              },
              Package(sz) {0,1,2,3, 0xab03008a,
              },
              Package(sz) {0,1,2,3, 0xab03008b,
              },
              0xab020022
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03008c,
              },
              Package(sz) {0,1,2,3, 0xab03008d,
              },
              Package(sz) {0,1,2,3, 0xab03008e,
              },
              Package(sz) {0,1,2,3, 0xab03008f,
              },
              0xab020023
            },
            0xab010008
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030090,
              },
              Package(sz) {0,1,2,3, 0xab030091,
              },
              Package(sz) {0,1,2,3, 0xab030092,
              },
              Package(sz) {0,1,2,3, 0xab030093,
              },
              0xab020024
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030094,
              },
              Package(sz) {0,1,2,3, 0xab030095,
              },
              Package(sz) {0,1,2,3, 0xab030096,
              },
              Package(sz) {0,1,2,3, 0xab030097,
              },
              0xab020025
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab030098,
              },
              Package(sz) {0,1,2,3, 0xab030099,
              },
              Package(sz) {0,1,2,3, 0xab03009a,
              },
              Package(sz) {0,1,2,3, 0xab03009b,
              },
              0xab020026
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab03009c,
              },
              Package(sz) {0,1,2,3, 0xab03009d,
              },
              Package(sz) {0,1,2,3, 0xab03009e,
              },
              Package(sz) {0,1,2,3, 0xab03009f,
              },
              0xab020027
            },
            0xab010009
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300a0,
              },
              Package(sz) {0,1,2,3, 0xab0300a1,
              },
              Package(sz) {0,1,2,3, 0xab0300a2,
              },
              Package(sz) {0,1,2,3, 0xab0300a3,
              },
              0xab020028
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300a4,
              },
              Package(sz) {0,1,2,3, 0xab0300a5,
              },
              Package(sz) {0,1,2,3, 0xab0300a6,
              },
              Package(sz) {0,1,2,3, 0xab0300a7,
              },
              0xab020029
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300a8,
              },
              Package(sz) {0,1,2,3, 0xab0300a9,
              },
              Package(sz) {0,1,2,3, 0xab0300aa,
              },
              Package(sz) {0,1,2,3, 0xab0300ab,
              },
              0xab02002a
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300ac,
              },
              Package(sz) {0,1,2,3, 0xab0300ad,
              },
              Package(sz) {0,1,2,3, 0xab0300ae,
              },
              Package(sz) {0,1,2,3, 0xab0300af,
              },
              0xab02002b
            },
            0xab01000a
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300b0,
              },
              Package(sz) {0,1,2,3, 0xab0300b1,
              },
              Package(sz) {0,1,2,3, 0xab0300b2,
              },
              Package(sz) {0,1,2,3, 0xab0300b3,
              },
              0xab02002c
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300b4,
              },
              Package(sz) {0,1,2,3, 0xab0300b5,
              },
              Package(sz) {0,1,2,3, 0xab0300b6,
              },
              Package(sz) {0,1,2,3, 0xab0300b7,
              },
              0xab02002d
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300b8,
              },
              Package(sz) {0,1,2,3, 0xab0300b9,
              },
              Package(sz) {0,1,2,3, 0xab0300ba0,
              },
              Package(sz) {0,1,2,3, 0xab0300bb,
              },
              0xab02002e
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300bc,
              },
              Package(sz) {0,1,2,3, 0xab0300bd,
              },
              Package(sz) {0,1,2,3, 0xab0300be,
              },
              Package(sz) {0,1,2,3, 0xab0300bf,
              },
              0xab02002f
            },
            0xab01000b
          },
          0xab000002
        },
        Package(sz) {
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300c0,
              },
              Package(sz) {0,1,2,3, 0xab0300c1,
              },
              Package(sz) {0,1,2,3, 0xab0300c2,
              },
              Package(sz) {0,1,2,3, 0xab0300c3,
              },
              0xab020030
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300c4,
              },
              Package(sz) {0,1,2,3, 0xab0300c5,
              },
              Package(sz) {0,1,2,3, 0xab0300c6,
              },
              Package(sz) {0,1,2,3, 0xab0300c7,
              },
              0xab020031
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300c8,
              },
              Package(sz) {0,1,2,3, 0xab0300c9,
              },
              Package(sz) {0,1,2,3, 0xab0300ca,
              },
              Package(sz) {0,1,2,3, 0xab0300cb,
              },
              0xab020032
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300cc,
              },
              Package(sz) {0,1,2,3, 0xab0300cd,
              },
              Package(sz) {0,1,2,3, 0xab0300ce,
              },
              Package(sz) {0,1,2,3, 0xab0300cf,
              },
              0xab020033
            },
            0xab01000c
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300d0,
              },
              Package(sz) {0,1,2,3, 0xab0300d1,
              },
              Package(sz) {0,1,2,3, 0xab0300d2,
              },
              Package(sz) {0,1,2,3, 0xab0300d3,
              },
              0xab020034
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300d4,
              },
              Package(sz) {0,1,2,3, 0xab0300d5,
              },
              Package(sz) {0,1,2,3, 0xab0300d6,
              },
              Package(sz) {0,1,2,3, 0xab0300d7,
              },
              0xab020035
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300d8,
              },
              Package(sz) {0,1,2,3, 0xab0300d9,
              },
              Package(sz) {0,1,2,3, 0xab0300da,
              },
              Package(sz) {0,1,2,3, 0xab0300db,
              },
              0xab020036
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300dc,
              },
              Package(sz) {0,1,2,3, 0xab0300dd,
              },
              Package(sz) {0,1,2,3, 0xab0300de,
              },
              Package(sz) {0,1,2,3, 0xab0300df,
              },
              0xab020037
            },
            0xab01000d
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300e0,
              },
              Package(sz) {0,1,2,3, 0xab0300e1,
              },
              Package(sz) {0,1,2,3, 0xab0300e2,
              },
              Package(sz) {0,1,2,3, 0xab0300e3,
              },
              0xab020038
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300e4,
              },
              Package(sz) {0,1,2,3, 0xab0300e5,
              },
              Package(sz) {0,1,2,3, 0xab0300e6,
              },
              Package(sz) {0,1,2,3, 0xab0300e7,
              },
              0xab020039
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300e8,
              },
              Package(sz) {0,1,2,3, 0xab0300e9,
              },
              Package(sz) {0,1,2,3, 0xab0300ea,
              },
              Package(sz) {0,1,2,3, 0xab0300eb,
              },
              0xab02003a
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300ec,
              },
              Package(sz) {0,1,2,3, 0xab0300ed,
              },
              Package(sz) {0,1,2,3, 0xab0300ee,
              },
              Package(sz) {0,1,2,3, 0xab0300ef,
              },
              0xab02003b
            },
            0xab01000e
          },
          Package(sz) {
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300f0,
              },
              Package(sz) {0,1,2,3, 0xab0300f1,
              },
              Package(sz) {0,1,2,3, 0xab0300f2,
              },
              Package(sz) {0,1,2,3, 0xab0300f3,
              },
              0xab02003c
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300f4,
              },
              Package(sz) {0,1,2,3, 0xab0300f5,
              },
              Package(sz) {0,1,2,3, 0xab0300f6,
              },
              Package(sz) {0,1,2,3, 0xab0300f7,
              },
              0xab02003d
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300f8,
              },
              Package(sz) {0,1,2,3, 0xab0300f9,
              },
              Package(sz) {0,1,2,3, 0xab0300fa,
              },
              Package(sz) {0,1,2,3, 0xab0300fb,
              },
              0xab02003e
            },
            Package(sz) {
              Package(sz) {0,1,2,3, 0xab0300fc,
              },
              Package(sz) {0,1,2,3, 0xab0300fd,
              },
              Package(sz) {0,1,2,3, 0xab0300fe,
              },
              Package(sz) {0,1,2,3, 0xab0300ff,
              },
              0xab02003f
            },
            0xab01000f
          },
          0xab000003
        },
        0xabababab
      })

	Name(pIR0, Package(4) {
		Package(4) {},
		Package(16) {},
		Package(64) {},
		Package(256) {}
		})
	Name(pIR1, Package(4) {
		Package(4) {},
		Package(16) {},
		Package(64) {},
		Package(256) {}
		})

	Name(pHR1, Package(1) {})
	Name(pHR2, Package(1) {})

	Add(iint, 1, iirf)

	Concatenate("chn0 of model is equal to ", chn0, Debug)

	/*
	 * ########## References to pkg-nodes inside one hierarchy ##########
	 */

SRMT("gen-inner-refs-to-pkg-nodes-of-pHR0")

	/*
	 * Generate references to chn0-number elements of all pkg-nodes of pHR0
	 * and pack up them per-level into pIR0.
	 */
	mfdd(RefOf(pHR0), pIR0, chn0, iint)

	/*
	 * Put elements of package pIR0 (references) into relevant elements
	 * of pkg-nodes of pHR0.
	 */
	mfdf(pIR0, RefOf(pHR0), chn0, iirf)

SRMT("verify-0-of-pHR0-by-inner-refs")

	/*
	 * Verify the contents of pHR0 (Integer-IDs of pkg-nodes)
	 * by read access through References packed into all its pkg-nodes.
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  0 - type of current (read) Integer-IDs
	 */
	mfe1(pHR0, chn0, iirf, HR00, 0, iint)

SRMT("rewrite-1-Integer-IDs-of-pHR0")

	/*
	 * Rewrite Integer-IDs for all pkg-nodes of hierarchy (pHR0) -
	 * read previous value, generate new and write back to pkg-node.
	 *
	 *  re-write I-ID: 1 - type of new (re-write) Integer-IDs
	 */
	Or(OP01, 0x100000, Local0)	// re-write I-ID + type of new (re-write) Integer-IDs
	mfe4(RefOf(pHR0), chn0, iint, iirf, Local0)

SRMT("verify-1-of-pHR0-by-inner-refs")

	/*
	 * Verify the new Integer-IDs of hierarchy.
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  1 - type of current (read) Integer-IDs
	 */
	Or(0, 0x10000, Local0)	// type of current (read) Integer-IDs
	mfe1(pHR0, chn0, iirf, HR00, Local0, iint)

SRMT("rewrite-pkg-nodes-of-pHR0")

	/*
	 * Rewrite the whole pkg-nodes of hierarchy -
	 * take each pkg-node and re-write it back to the same location.
	 *
	 *  re-write pkg-nodes
	 */
	mfe4(RefOf(pHR0), chn0, iint, iirf, OP02)

SRMT("verify-1-of-pHR0-by-inner-refs")

	/*
	 * Verify Integer-IDs of hierarchy: nothing should change.
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  1 - type of current (read) Integer-IDs
	 */
	Or(0, 0x10000, Local0)	// type of current (read) Integer-IDs
	mfe1(pHR0, chn0, iirf, HR00, Local0, iint)

	/*
	 * ############# Duplicate of hierarchy #############
	 */

SRMT("Duplicate-pHR0-to-pHR1")

	/*
	 * Copy hierarchy to another object
	 */
	Store(pHR0, pHR1)

	/*
	 * Verify Integer-IDs of both instances of hierarchy:
	 * nothing should change. References of both hierarchies
	 * point to the same pkg-nodes, so, Integer-IDs should
	 * be the same.
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  1 - type of current (read) Integer-IDs
	 */
	Or(0, 0x10000, Local0)	// type of current (read) Integer-IDs
SRMT("verify-1-of-pHR0-by-inner-refs")
	mfe1(pHR0, chn0, iirf, HR00, Local0, iint)
SRMT("verify-1-of-pHR0-by-inner-refs-duplicated-to-pHR1")
	mfe1(pHR1, chn0, iirf, HR00, Local0, iint)


SRMT("rewrite-2-Integer-IDs-of-pHR0")

	/*
	 * Rewrite Integer-IDs for all pkg-nodes of source hierarchy.
	 *
	 *  re-write I-ID: 2 - type of new (re-write) Integer-IDs
	 */
	Or(OP01, 0x200000, Local0)	// re-write I-ID + type of new (re-write) Integer-IDs
	mfe4(RefOf(pHR0), chn0, iint, iirf, Local0)

	/*
	 * Verify new Integer-IDs through the References of both hierarchies
	 * (both point to the same pkg-nodes).
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  2 - type of current (read) Integer-IDs
	 */
	Or(0, 0x20000, Local0)	// type of current (read) Integer-IDs
SRMT("verify-2-of-pHR0-by-inner-refs")
	mfe1(pHR0, chn0, iirf, HR00, Local0, iint)
SRMT("verify-2-of-pHR0-by-inner-refs-duplicated-to-pHR1")
	mfe1(pHR1, chn0, iirf, HR00, Local0, iint)

SRMT("rewrite-inner-references-of-pHR0")

	/*
	 * Rewrite all references present in pkg-nodes of hierarchy pHR0 -
	 * take each reference and re-write it back to the same location.
	 *
	 *  re-write references
	 */
	mfe4(RefOf(pHR0), chn0, iint, iirf, OP03)

	/*
	 * Verify Integer-IDs of both instances of hierarchy: nothing should change.
	 *
	 * mfe1() does reading unconditionally:
	 *  read:  2 - type of current (read) Integer-IDs
	 */
	Or(0, 0x20000, Local0)	// type of current (read) Integer-IDs
SRMT("verify-2-of-pHR0-by-inner-refs")
	mfe1(pHR0, chn0, iirf, HR00, Local0, iint)
SRMT("verify-2-of-pHR0-by-inner-refs-duplicated-to-pHR1")
	mfe1(pHR1, chn0, iirf, HR00, Local0, iint)

	/*
	 * #######                    Cross references                    #######
	 * #######                                                        #######
	 * ####### References to pkg-nodes inside each of two hierarchies #######
	 * #######  added with references between those two hierarchies. #######
	 */

SRMT("Duplicate-pHR0-to-pHR2")

	/*
	 * Copy hierarchy to another object
	 */
	Store(pHR0, pHR2)

SRMT("gen-inner-refs-to-pkg-nodes-of-pHR2")

	/*
	 * Generate references to chn0-number elements of all pkg-nodes of pHR2
	 * and pack up them per-level into pIR1.
	 */
	mfdd(RefOf(pHR2), pIR1, chn0, iint)

	/*
	 * Put elements of package pIR1 (references) into relevant elements
	 * of pkg-nodes of pHR2.
	 */
	mfdf(pIR1, RefOf(pHR2), chn0, iirf)

	/* ===== Add cross references between two hierarchies, (pHR0 & pHR2) ===== */

SRMT("add-inner-refs-to-pkg-nodes-of-pHR2-into-pHR0")

	/*
	 * Put references to pkg-nodes of pHR2 into nodes of pHR0.
	 */
	mfdf(pIR1, RefOf(pHR0), chn0, icrf)

SRMT("add-inner-refs-to-pkg-nodes-of-pHR0-into-pHR2")

	/*
	 * Put references to pkg-nodes of pHR0 into nodes of pHR2.
	 */
	mfdf(pIR0, RefOf(pHR2), chn0, icrf)

	/* Re-write + Verify Integer-IDs */

SRMT("rewrite-3-Integer-IDs-of-pHR2")
	Or(OP01, 0x300000, Local0)
	mfe4(RefOf(pHR2), chn0, iint, iirf, Local0)
SRMT("verify-3-of-pHR2-by-cross-refs-of-pHR0")
	Or(0, 0x30000, Local0)
	mfe1(pHR0, chn0, icrf, HR00, Local0, iint)
SRMT("verify-2-of-pHR0-by-cross-refs-of-pHR2")
	Or(0, 0x20000, Local0)
	mfe1(pHR2, chn0, icrf, HR00, Local0, iint)
SRMT("rewrite-4-Integer-IDs-of-pHR0")
	Or(OP01, 0x400000, Local0)
	mfe4(RefOf(pHR0), chn0, iint, iirf, Local0)
SRMT("verify-4-of-pHR0-by-cross-refs-of-pHR2")
	Or(0, 0x40000, Local0)
	mfe1(pHR2, chn0, icrf, HR00, Local0, iint)

	/* Re-write pkg-nodes + Verify */

SRMT("rewrite-pkg-nodes-of-pHR0")
	mfe4(RefOf(pHR0), chn0, iint, icrf, OP02)
SRMT("rewrite-pkg-nodes-of-pHR2")
	mfe4(RefOf(pHR2), chn0, iint, icrf, OP02)
SRMT("verify-3-of-pHR2-by-cross-refs-of-pHR0")
	Or(0, 0x30000, Local0)
	mfe1(pHR0, chn0, icrf, HR00, Local0, iint)
SRMT("verify-4-of-pHR0-by-cross-refs-of-pHR2")
	Or(0, 0x40000, Local0)
	mfe1(pHR2, chn0, icrf, HR00, Local0, iint)

	/* Re-write inner references + Verify */
	/* Re-write cross references + Verify */

SRMT("rewrite-inner-references-of-pHR0")
	mfe4(RefOf(pHR0), chn0, iint, iirf, OP03)
SRMT("rewrite-inner-references-of-pHR2")
	mfe4(RefOf(pHR2), chn0, iint, iirf, OP03)
SRMT("rewrite-cross-references-of-pHR0")
	mfe4(RefOf(pHR0), chn0, iint, icrf, OP03)
SRMT("rewrite-cross-references-of-pHR2")
	mfe4(RefOf(pHR2), chn0, iint, icrf, OP03)

SRMT("verify-3-of-pHR2-by-cross-refs-of-pHR0")
	Or(0, 0x30000, Local0)
	mfe1(pHR0, chn0, icrf, HR00, Local0, iint)
SRMT("verify-4-of-pHR0-by-cross-refs-of-pHR2")
	Or(0, 0x40000, Local0)
	mfe1(pHR2, chn0, icrf, HR00, Local0, iint)
}

Method(mfdb)
{
	CH03("", 0, 0x200, __LINE__, 0)
	mfdc()
	CH03("", 0, 0x202, __LINE__, 0)
}
