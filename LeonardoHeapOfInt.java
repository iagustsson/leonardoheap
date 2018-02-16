/*
 * Copyright 2017 Ingolfur Agustsson
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or
 * sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 *
 */
package com.iagustsson.leonardoheap;

import java.util.Arrays;
import java.util.Random;
import java.util.function.IntBinaryOperator;
import java.util.stream.IntStream;
import java.util.stream.Stream;


/**
 * This class implements the implicit heap data structure that was
 * invented and published by E. W. Dijkstra in 1981 when implementing
 * smoothsort (Smoothsort, an alternative for sorting in situ [EWD82]).
 * @see <a href="http://www.cs.utexas.edu/~EWD/transcriptions/EWD07xx/EWD796a.html">Java Spec</a>
 *
 * <p>Smoothsort is an in-place sorting algorithm that is a variant
 * of heapsort. Like heapsort, smoothsort has the general characteristic
 * of O(n⋅log(n)) when sorting n elements, but for an input that is
 * initially (nearly) sorted, smoothsort is of order O(n), "with a
 * smooth transition between the two, hence its name" [EWD82].
 * @see <a href="https://en.wikipedia.org/wiki/Smoothsort">Java Spec</a>
 *
 * @author Ingolfur Agustsson
 * @version 1.1 01/26/18
 */
public class LeonardoHeapOfInt {
    // Leonardo numbers are given by:
    //    LP[0] = LP[1] = 1 and LP[t+2] = LP[t+1]+LP[t]+1
    // Nb. Since  LP[t] = LP[t+2]-LP[t+1]-1, we also have
    //    LP[-1] = LP[1]-LP[0]-1 = -1, and
    //    LP[-2] = LP[0]-LP[-1]-1 = 1-(-1)-1 = 1
    // Also sum_{t=0}^{n} LP[t] = LP[n+2]-n-2

    // calculate all Leonardo numbers less than MAX_INT
    private final static int[] LP = Stream
            .iterate(new long[]{1, 1}, s -> new long[]{s[1], s[0] + s[1] + 1L})
            .mapToLong(n -> n[0]).takeWhile(lll -> lll < (long) Integer.MAX_VALUE)
            .mapToInt(lll -> (int) lll).toArray();

    // x is the binary representation of the heap data structure which keeps
    // track of all of the trees that are being used in the Leonardo heap.
    // The binary representation can be defined in terms of s and t, where
    // t is the # of trailing zeros (those to the right of the last non-zero bit),
    // and s is the bit pattern of x, less trailing zeros, omitting the least non-zero
    // bit of s since it is always 1 (except when x is 0). Therefore the binary
    // representation in terms of s and t is given by:
    //   x = ((s<<1) | 0b1) << t
    //
    // EXAMPLE:
    // x |  bits | s  | t
    // --|-------|----|---
    // 0 | 00000 |  0 | 0
    // 1 | 00010 |  0 | 1
    // 2 | 00011 |  1 | 0
    // 3 | 00100 |  0 | 2
    // 4 | 00110 |  1 | 1
    // 5 | 01000 |  0 | 3
    // 6 | 01010 | 10 | 1
    // 7 | 01011 |101 | 0
    // 8 | 01100 |  1 | 2
    // 9 | 10000 |  0 | 4
    // ...
    //  7049154 |  0 11000000 00000000 00000000 00000000 | 1 | 30
    //  7049155 |  1 00000000 00000000 00000000 00000000 | 0 | 32
    // ...
    // 11405772 |  1 10000000 00000000 00000000 00000000 | 1 | 31
    // 11405773 | 10 00000000 00000000 00000000 00000000 | 0 | 33
    //------------- limit when using 32-bits for s ----------------
    // ...
    // 2147483647 | 10101000000001010100001010100100001000001100 | 1443285518401 | 2
    //----------------- limit for Java arrays -----------------
    //
    private long s;
    private int t;

    // the actual sub-array to be implicitly reconfigured
    // into a Leonardo heap is m[left, right]
    private final int[] m;
    // the index of the first element, inclusive, to be sorted
    final int left;
    // the index of the last element, inclusive, to be sorted
    int right;
    // the comparator that specifies the order within the heap
    private IntBinaryOperator cmp;

    /*
     * Incorporates the given array of integers into a Leonardo heap
     * according to the order induced by the specified comparator.
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param fromIndex the index of the first element, inclusive, to be sorted
     * @param toIndex the index of the last element, exclusive, to be sorted
     * @param cmp the comparator to determine the order within the heap.
     *        (the comparator is IntBinaryOperator that compares its two
     *        argument for order, such that the first argument is less extreme
     *        than, equally extreme as, or more extreme than the second argument,
     *        depending on if the returned integer < 0, 0, or > 0).
     *
     * @throws IllegalArgumentException if {@code fromIndex > toIndex}
     * @throws ArrayIndexOutOfBoundsException
     *     if {@code fromIndex < 0} or {@code toIndex > a.length}
     */
    public LeonardoHeapOfInt(int[] a, int fromIndex, int toIndex, IntBinaryOperator cmp) {
        rangeCheck(a.length, fromIndex, toIndex);
        this.m = a;
        this.left = fromIndex;
        this.cmp = cmp;
        // create a heap out of the given array of elements
        // setting s, t and the right variable in the process
        heapify(toIndex);
    }

    /**
     * Checks that {@code fromIndex} and {@code toIndex} are in
     * the range and throws an exception if they aren't.
     */
    static void rangeCheck(int arrayLength, int fromIndex, int toIndex) {
        if (fromIndex > toIndex) {
            throw new IllegalArgumentException("fromIndex(" + fromIndex + ") > toIndex(" + toIndex + ")");
        }
        if (fromIndex < 0) {
            throw new ArrayIndexOutOfBoundsException(fromIndex);
        }
        if (toIndex > arrayLength) {
            throw new ArrayIndexOutOfBoundsException(toIndex);
        }
    }

    /**
     * Builds a Leonardo heap by reordering the elements in the given array, m,
     * ensuring the order-property between all the trees being used
     * (as recorded by s and t), and that the heap-property is maintained
     * for each tree and their subtrees.
     *
     * <p>Builds a heap from the given array, m, with n=m.length elements.
     * When n < 2, the heap is either empty or a single element, otherwise
     * this method starts with a heap of the first two elements, then
     * iteratively inserts each successive element (except the last one)
     * into the heap. At the beginning of the i-th iteration,
     * the heap contains all the elements m[0], m[1], ..., m[i], and the
     * bit pattern of x (in terms of s and t) records the tree structure
     * of all of those elements within the heap (meaning that x is
     * post-increment at the end of the loop). The bulk of the work,
     * during each iteration, goes into keeping sufficient properties
     * of the heap invariant to maintain its tree structure (see EWD82).
     * The loop maintains the heap-property (i.e. the value of each node
     * is less or equally extreme as the value of its parent) of all
     * the trees in the heap. Also when encountering trees that will
     * not be merged into a larger one at later iteration, the loop
     * restores the order-property (i.e. the roots of the trees in the heap
     * form a monotone sequence where each tree is more or equally extreme
     * to the root of its left neighboring tree) of the trees in the heap.
     * After the loop ends, the last element is inserted and the order-
     * property restored, thus, leaving the heap in a state of fulfilling
     * both the heap-and the order-property.
     */
    private void heapify(int toIndex) {
        this.right = toIndex-1;
        if (left == right) {
            this.s = 0b0;
            this.t = 0;
            // heap is ready
        } else if (left+1 == right) {
            // m is a single-element Leonardo tree and by convention it is
            // represented as a single stretch of order 1 and size LP[1]
            this.s = 0b0;
            this.t = 1;
            // heap is ready
        } else {
            // initially x=0b11 to reflect that the heap already contains m[left],
            // and the first thing happening in the loop is the inclusion of m[left+1]
            this.s = 0b1;
            this.t = 0;

            for (int i = left+1; i < right; ++i) {
                // now m[i] is the root value of a Leonardo tree of order t and size LP[t],
                // however, m[i] is not necessarily in the correct position within LP[t],
                // and the roots of the trees in the heap are not necessarily properly
                // ordered, in the relation with this newly inserted element

                if ((s & 0b1) == 0b1) { // ; if p mod 8 = 3 [EWD82]
                    // now both LP[t] and LP[t+1] are being used in the heap,
                    // and they are the two rightmost trees in the heap.

                    // sift m[i] down to its correct position within LP[t]
                    sift(m, i, t, cmp);
                    // the loop maintains the heap-property
                    assert (checkHeapProperty(m, i, s, t, cmp));

                    // perform x++, i.e. advance the bitvector to be ready to receive
                    // element m[i+1] in the next iteration, i.e. merge
                    // m[i+1], LP[t+1] and LP[t] into LP[t+2]
                    s >>>= 2;
                    t = t + 2;
                } else {
                    assert (t > 0);

                    // if LP[t] is going to be merged at some later iteration,
                    // it will need to include a tree of size c=LP[t-1],
                    // i.e. "# elements left to add" ≥ c+1 (or endIndex-i≥c+1).
                    final int c = LP[t - 1];
                    if (i + c < right) {   // if q + c < N → sift [EWD82]
                        // sift m[i] down to its correct position,
                        // and restore the heap property
                        sift(m, i, t, cmp);
                        // the loop maintains the heap-property
                        assert (checkHeapProperty(m, i, s, t, cmp));
                    } else { // [] q + c ≥ N → trinkle [EWD82]
                        // LP[t] will not be merged at some later iteration,
                        // and will be present in the bitvector at the
                        // end of the loop.

                        // move the root of LP[t] (i.e. the value of m[i]),
                        // to its appropriate position in the sequence
                        // of less extreme roots, and sift it down
                        // to its correct position, thus
                        // restore the heap- and order-property
                        trinkle(m, i, s, t, cmp);
                        // the loop restores the order-property to trees
                        // that have reached their final size
                        assert (checkOrderProperty(m, i, s, t, cmp));
                    }

                    // perform x++, i.e. advance the bitvector such
                    // that in the next iteration, the next element,
                    // m[i+1], will be the root of LP[1] (or LP[0]).
                    if (t != 1) {
                        // if this point is reached, LP[1] is available
                        // for m[i+1] in the next iteration

                        // reconfigure s and t accordingly
                        s = ((s << 1) | 0b1) << (t - 2);
                        t = 1;
                    } else {
                        // if this point is reached, LP[1] is in use
                        // but LP[0] must be available for m[i+1]
                        // in the next iteration

                        // reconfigure s and t accordingly
                        t = 0;
                        s = (s << 1) | 0b1;
                    }
                }

            }
            // since s and t are post-incremental after each iteration,
            // they are already appropriate for the last element

            // with the inclusion of the last element, the heap has reached its final
            // size, so we trinkle the whole heap so that its trees become properly
            // ordered and the last element is appropriately placed.
            trinkle(m, right, s, t, cmp);

            assert (checkHeapProperty(m, right, s, t, cmp));
            assert (checkOrderProperty(m, right, s, t, cmp));
            // heap is ready
        }
    }

    /*
     * Sifts m[i] down to its appropriate place within tree LP[t]
     * to restore the heap-property.
     * <p>
     * The operation sift is defined as follows (EWD82):
     * "sift applied to an element without larger sons is a skip, sift applied to an
     * element m(r1) that is exceeded by its largest son m(r2) consists of a swap of
     * these two values, followed by an application of sift to m(r2).
     * <p>
     * The given stretch is a contiguous subarray m[i-LP[t-1]-LP[t-2], i]
     * which represents an implicit Leonardo tree of order t and size LP[t]
     * rooted at position i. For t≥2, the stretch consists of:
     *    a left Leonardo subtree of size LP[t−1] rooted at i-1-LP[t-2], followed by
     *    a right Leonardo subtree of size LP[t−2] rooted at i-1, followed by
     *    the root node at i (the rightmost element).
     * For a stretch to be a trusty one, the roots of both subtrees cannot exceed the root,
     * and to restore the heap-property the rightmost stretch is made into a trusty one by
     * applying this operation, sift.
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param i index of current element to be sifted down
     * @param t is the order of the tree that m[i] gets sifted down into
     * @param cmp specifies the order within the heap
     */
    private static void sift(final int[] m, int i, int t, IntBinaryOperator cmp) {
        // preserve the original root value
        final int root = m[i];
        while (t > 1) {
            // the left subtree, LP[t−1], is rooted at
            final int j = i - LP[t - 2] - 1;
            // the right subtree, LP[t−2], is rooted at
            final int k = i - 1;

            assert (j >= 0 && k >= 0);

            if (cmp.applyAsInt(root, m[j]) >= 0 && cmp.applyAsInt(root, m[k]) >= 0) {
                // the root value of neither subtrees exceeds the original root value
                break;
            }

            if (cmp.applyAsInt(m[j], m[k]) >= 0) {
                // if this point is reached, the root of the left subtree is the larger of the two

                // swap the value at the root of the current stretch
                // with the value at the root of the its left subtree
                m[i] = m[j];

                // next round of iteration, applies sift to the
                // left subtree (the larger of the two subtrees)
                // which is rooted at position j and of order t-1
                i = j;
                t = t - 1;
            } else {
                // if this point is reached, the root of the right subtree is the larger of the two

                // swap the value at the root of the current stretch
                // with the value at the root of the its right subtree
                m[i] = m[k];

                // next round of iteration, applies sift to the
                // right subtree (the smaller of the two subtrees)
                // which is rooted at position k and of order t-2
                i = k;
                t = t - 2;
            }
        }
        // finally swap the original root into the position of the last stretch
        m[i] = root;
    }

    /*
     * Trinkle m[i] (which is the root of LP[t]) to its appropriate place in the
     * heap to restore the order-property and maintain the heap-property.
     * <p>
     * The operation trinkle is defined as follows (EWD82):
     * "trinkle is very similar to sift when we regard each stretch root as the stepson
     * of the root of the stretch to its right. Applied to a root without larger sons,
     * trinkle is a skip; otherwise the root is swapped with its largest son, etc.
     * The trouble with the code is that all sorts of sons may be missing. In the following,
     * trinkle is eventually reduced to a sift, viz. when the stepson relation is no longer
     * of interest."
     *
     * "trinkle is like sift, be it for a partly ternary tree":
     * <- LP[?] -> | <------ L[t-1] ------> | <- L[t-2] -> | root |
     * ... , i-LP[t], ...., i - 1 - LP[t - 2],    ...,   i-1,   i
     *         ﹀                 ﹀                      ﹀
     *         i3                 j                       k
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param i index of current element to be sifted down
     * @param s is the bit pattern of x, less trailing zeros and
     *        the last non-zero bit
     * @param t is the number of trailing zeros in the bit pattern x
     *        and the order of the tree that m[i] is the root of
     * @param cmp specifies the order within the heap
     */
    private static void trinkle(final int[] m, int i, long s, int t, IntBinaryOperator cmp) {
        // preserve the original root value
        final int root = m[i];

        for(int trail; s!=0; trail = Long.numberOfTrailingZeros(s) + 1, s >>>= trail, t += trail) {
            // when this point is reached we have a stretch rooted at m[i] of length LP[t]
            // that can be broken down into <LP[t-1]><LP[t-2]><m[i]> where the right subtree,
            // LP[t−2], is rooted at i-1, and the left subtree, LP[t-1], at i - LP[t - 2] - 1

            // find the index, i3, of the root of the second-to-rightmost tree in the heap
            int i3 = i - LP[t];
            // regard m[i3] as the third side subtree (stepchild) of the stretch to its right
            if (cmp.applyAsInt(root, m[i3]) >= 0) {
                // root does not need to trinkled further
                break;
            }
            // if this point is reached, m[i3] is more extreme than root, so in case
            // m[i3] is also more extreme than both its children (if there any),
            // we can break the loop, otherwise, we set m[i]=m[i3] (which does not
            // violate the heap-property of LP[t]), and continue

            if (t > 1) {
                final int k = i - 1;
                if (cmp.applyAsInt(m[k], m[i3]) >= 0) {
                    break;
                }
                final int j = i - LP[t - 2] - 1;
                if (cmp.applyAsInt(m[j], m[i3]) >= 0) {
                    break;
                }
            }
            m[i] = m[i3];
            i = i3;
        }
        m[i] = root;
        sift(m, i, t, cmp);
    }

    /*
     * Check if all the trees used in the heap and all their sub-trees fulfill
     * the heap-property.
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param i the index of last element to be added to the heap
     * @param s is the bit pattern of x, less trailing zeros and
     *        the last non-zero bit
     * @param t is the number of trailing zeros in the bit pattern x
     * @param cmp specifies the order within the heap
     * @return true if all the trees and sub-trees in the heap fulfill the heap-property
     */
    private static boolean checkHeapProperty(int[] m, int i, long s, int t, IntBinaryOperator cmp) {
        for(int trail; s!=0; i -= LP[t], trail = Long.numberOfTrailingZeros(s) + 1, s >>>= trail, t += trail) {
            if (!checkHeapProperty(m, i, t, cmp)) {
                return false;
            }
        }
        return true;
    }

    /*
     * Recursively, check if the tree of size LP[t] and all its sub-trees fulfill
     * the heap-property.
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param i the index of last element to be added to the heap
     * @param t is the order of the tree being checked
     * @param cmp specifies the order within the heap
     * @return true if LP[t] and its sub-trees fulfill the heap-property
     */
    private static boolean checkHeapProperty(int[] m, int i, int t, IntBinaryOperator cmp) {
        if (t <= 1) return true;
        if (t == 2) {
            return cmp.applyAsInt(m[i], m[i - 1]) >= 0;
        }
        final int root = m[i];
        // the left subtree, LP[t−1], is rooted at
        final int j = i - LP[t - 2] - 1;
        // the right subtree, LP[t−2], is rooted at
        final int k = i - 1;

        if (cmp.applyAsInt(root, m[j]) >= 0 && cmp.applyAsInt(root, m[k]) >= 0 && checkHeapProperty(m, j, t - 1, cmp) && checkHeapProperty(m, k, t - 2, cmp)) {
            return true;
        }
        assert false : String.format("FAILED: Heap-property for tree LP[%d] rooted at i=%d since the root of either of its subtrees is more extreme!", t, i);
        // this point is only reached if the above assertion fails
        return false;
    }

    /*
     * Check if all the trees used in the heap and all their sub-trees fulfill
     * the order-property.
     *
     * @param m the array to be implicitly reconfigured into a heap
     * @param i the index of last element to be added to the heap
     * @param s is the bit pattern of x, less trailing zeros and
     *        the last non-zero bit
     * @param t is the number of trailing zeros in the bit pattern x
     * @param cmp specifies the order within the heap
     * @return true if all the trees and sub-trees in the heap fulfill the order-property
     */
    private static boolean checkOrderProperty(int[] m, int i, long s, int t, IntBinaryOperator cmp) {
        int rightMoreExtreme = m[i];
        for (int trail; s != 0; i -= LP[t], trail = Long.numberOfTrailingZeros(s) + 1, s >>>= trail, t += trail) {
            if (cmp.applyAsInt(rightMoreExtreme, m[i]) < 0) {
                assert false : String.format("FAILED: Order-property for tree LP[%d] rooted at i=%d is more extreme than its left neighbor!", t, i);
                // this point is only reached if the above assertion fails
                return false;
            }
            rightMoreExtreme = m[i];
        }
        return true;
    }

    /*
     * Check if the heap is empty.
     *
     * @return true if no trees are in use by the heap
     */
    public boolean isEmpty() {
        return this.s == 0b0 && this.t <= 0;
    }

    /*
     * swap the values of the two integers with indices lhs and rhs in array arr
     * i.e. arr[lhs], arr[rhs] := arr[rhs], arr[lhs]
     *
     * @param arr the array to be implicitly reconfigured into a heap
     * @param lhs index of the left-hand side element to be swapped
     * @param rhs index of the left-hand side element to be swapped
     */
    private static void swap(final int[] arr, final int lhs, final int rhs) {
        final int temp = arr[lhs];
        arr[lhs] = arr[rhs];
        arr[rhs] = temp;
    }

    /*
     * Effectively removes the rightmost element, m[right], from the heap,
     * and restores the heap- and order-property among the rest of the heap.
     * <p>
     * Basically, at the beginning m[left], ..., m[right] are ordered such that
     * they fulfill both the heap- and order-property, and x = ((s<<1)|0b1)<<t
     * is the binary representation keeping track of all of the trees that are
     * used in the heap.
     * When the rightmost tree is either LP[0] or LP[1], m[right] is
     * the root of a singleton tree, and the heap- and order-property are
     * "maintained without further measures" (see EWD82).
     * Otherwise, m[right] is the root of the rightmost tree, LP[t], and
     * the removal of m[right] decomposes L[t] into LP[t-1] and LP[t-2].
     * The two new trees separately fulfill the heap-property, but the
     * order-property needs to be restored by trinkling their roots into
     * the appropriate trees and then sifting them down into the correct
     * position. This is accomplished by a slight variation of trinkle,
     * (called semitrinkle or pretrinkle in EWD82), that exploits the fact
     * that the two subtrees, LP[t-1] and LP[t-2], already fulfill the
     * heap-property (which allows for fewer comparisons than straight up
     * calling trinkle). The LP[t-2] becomes the new rightmost tree and
     * LP[t-1] the new second-to-rightmost tree. If present, the
     * third-to-righmost tree is LP[t+trail], where trail is the position of
     * the least significant non-zero in s, and it is rooted at i3=right-LP[t].
     * In case that the roots of LP[t-2], LP[t-1] and LP[t+trail] are more or
     * equally extreme as the root of each other, respectively, the heap- and
     * order-property are "maintained without further measures", but otherwise
     * their roots need to be switched around and other necessary changes to
     * restore those properties (see EWD82).
     * In the end, the index of the last element included in the heap is reduced
     * by one to complete the effective removal of the element that was the
     * rightmost in the heap at the beginning of calling this method.
     */
    private void pop() {
        if(isEmpty()) {
            // heap is already empty, nothing to pop off
            return;
        }
        if (t == 0) {
            assert (s & 0b1) == 0b1 : String.format("ERROR: Since right≥2, LP[0] cannot be present without LP[1] being present too ");
            assert (checkHeapProperty(m,right,s,t,cmp));
            assert (checkOrderProperty(m, right, s, t, cmp));

            // perform --x, i.e. reduce the bitvector by removing LP[0],
            // and making LP[1] the rightmost tree
            s >>>= 1;
            t = 1;
        } else if (t == 1) {
            assert (checkHeapProperty(m,right,s,t,cmp));
            assert (checkOrderProperty(m, right, s, t, cmp));

            // perform --x, i.e. reduce the bitvector by removing LP[1]
            // and advancing to the next tree to its left (if present)
            final int trail = (s!=0b0) ? Long.numberOfTrailingZeros(s) + 1 : -1;
            s >>>= trail;
            t += trail;
        } else {
            // if this point is reached, the rightmost tree, LP[t],
            // is decomposed into LP[t-1] and LP[t-2].

            // the new second-to-rightmost tree, LP[t−1], is rooted at
            final int j = right - LP[t - 2] - 1;
            // the new rightmost tree, LP[t−2], is rooted at
            final int k = right - 1;

            if (s != 0) {
                // the third-to-rightmost tree is rooted at
                final int i3 = right - LP[t];

                if (cmp.applyAsInt(m[i3], m[j]) > 0) {
                    // [] m(r1) > m(r)->m:swap(r,r1); trinkle [EWD86]

                    // swap the root of the second-to-rightmost tree
                    // with the root of the third-to-rightmost tree
                    swap(m, j, i3);

                    final int trail = Long.numberOfTrailingZeros(s) + 1;
                    trinkle(m, i3, s >>> trail, t + trail, cmp);
                } //; if m(r1)<=m(r)->skip [EWD86]

                //assert(cmp.applyAsInt(m[j], m[i3]) >= 0) : "ERROR: The second-to-rightmost tree must be more or equally extreme as the third-to-rightmost tree, to maintain order-property";
            }

            if (cmp.applyAsInt(m[j], m[k]) > 0) {
                // swap the root of the rightmost tree
                // with the root of the second-to-rightmost tree
                swap(m, k, j);
                // now m[j] is the less extreme of the two
                // and needs to be sifted down to its correct
                // position, and the whole heap trinkled to
                // restore order-property
                trinkle(m, j, s << 1, t - 1, cmp);
            }

            assert (checkHeapProperty(m,right,s,t,cmp));
            assert (checkOrderProperty(m, right, s, t, cmp));

            // perform --x, i.e. reduce the bitvector by removing LP[t]
            // and include LP[t-1] and LP[t-2] instead
            s = (s << 2) | 0b1;
            t = t - 2;
        }
        // afterwards, the rightmost element, m[i], has been
        // effectively popped from the heap.
        --right;
    }

    /*
     * Smoothsort is an in-place algorithm which sorts an array of n elements
     * by transforming the array into implicit Leonardo heap data using only
     * O(1) auxiliary data structure, offering on average O(n⋅log(n))
     * performance and best-case performance of O(n).
     *
     * @param a the array to be sorted using the Leonardo heap
     * @param fromIndex the index of the first element, inclusive, to be sorted
     * @param toIndex the index of the last element, exclusive, to be sorted
     * @param cmp specifies the order within the heap
     *
     * @throws IllegalArgumentException if {@code fromIndex > toIndex}
     * @throws ArrayIndexOutOfBoundsException
     *     if {@code fromIndex < 0} or {@code toIndex > a.length}
     */
    public static void smoothsort(int[] a, int fromIndex, int toIndex, IntBinaryOperator cmp) {
        if(fromIndex == toIndex) {
            // the sub-array to sort is empty, so nothing to do
            return;
        }
        LeonardoHeapOfInt lheap = new LeonardoHeapOfInt(a, fromIndex, toIndex, cmp);
        for(int i=toIndex; --i>=fromIndex; ) {
            // m[i] is the extreme of m[fromIndex], ..., m[i] (since throughout we
            // maintain both the heap- and the order-property).

            // pop the extreme from the heap, effectively removing the rightmost element
            lheap.pop();
        }
    }

    public static void main(String[] args) {
        final long startTime = System.nanoTime();

        final long seed = System.nanoTime();
        Random random = new Random(seed);

        final int N = (int) 1e6;

        // randomly selecting the number of elements to be sorted between 0 and N
        // in such away that each decade is equally likely
        final int M = (int)Math.pow(10.0, Math.log10(N)*random.nextDouble());
        //final int M = N;

        IntStream randIntStream = random.ints(0, M / 2); //999999

        // create an array of random integers to be sorted
        // starting at random index, toIndex, and ending at another random index, toIndex-1
        int[] a = randIntStream.limit(M).toArray();
        // for the testing purposes, the fromIndex is always found within the
        // first 0.1% of the number of elements, and toIndex within the
        // last 1% of the number of elements, so [fromIndex, toIndex-1]
        // covers most of [0,M-1], but not quite all of it
        final int fromIndex = (int) (0.001 * random.nextDouble() * M);
        final int toIndex = M - (int) (0.01 * random.nextDouble() * (M - fromIndex));

        System.err.println("Comparing smoothsort (using Leonardo heap) to regular array sort,");
        System.err.println("using array of random elements (random seed=" + seed + ").");
        System.err.println("This test randomly selects " + M + " elements between 0 and " + (M / 2) + ", puts them into");
        System.err.println("an array, and then only sorts those with indicies between " + fromIndex + " and " + toIndex + " (exclusive).");

        // create copy of the array that will be sorted by the Leonardo heap
        int[] heapArr = Arrays.copyOf(a, a.length);

        // sort the original array
        System.err.println(String.format("Before array sort, elapsed time:\t%.1f sec", (System.nanoTime() - startTime) / 1e9));
        Arrays.sort(a, fromIndex, toIndex);
        System.err.println(String.format("After array sort, elapsed time:\t%.1f sec", (System.nanoTime() - startTime) / 1e9));


        System.err.println(String.format("Before sorting using the Leonardo heap, elapsed time:\t%.1f sec", (System.nanoTime() - startTime) / 1e9));
        LeonardoHeapOfInt.smoothsort(heapArr, fromIndex, toIndex, (int lhs, int rhs) -> (lhs - rhs));
        System.err.println(String.format("Done sorting using the Leonardo heap, elapsed time:\t%.1f sec", (System.nanoTime() - startTime) / 1e9));

        System.err.println("Compare the sorting results");
        if (heapArr.length != a.length || IntStream.range(fromIndex, toIndex).anyMatch(iii -> heapArr[iii] != a[iii])) {
            System.err.println("ERROR: Arrays from heap sort and array sort differ.");
            IntStream.range(fromIndex, toIndex).filter(iii -> heapArr[iii] != a[iii])
                    .forEach(iii -> System.err.println("At index " + iii + " sorting via heap returns " + heapArr[iii] + " vs. " + a[iii]));
            System.exit(1);
        }
        System.err.print("SUCCESS: Arrays are identical, heap sort and array sort agree, ");
        System.err.println(String.format("elapsed time:\t%.1f sec", (System.nanoTime() - startTime) / 1e9));
    }
}
