#region License

/*
MIT License

Copyright(c) 2017-2020 Mattias Edlund

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
*/

#endregion

#region Original License

/////////////////////////////////////////////
//
// Mesh Simplification Tutorial
//
// (C) by Sven Forstmann in 2014
//
// License : MIT
// http://opensource.org/licenses/MIT
//
//https://github.com/sp4cerat/Fast-Quadric-Mesh-Simplification

#endregion

#if UNITY_2018_2_OR_NEWER
#define UNITY_8UV_SUPPORT
#endif

using System;
using System.Collections.Generic;
using System.Runtime.CompilerServices;
using UnityEngine;
using UnityMeshSimplifier.Internal;

namespace UnityMeshSimplifier
{
    internal class Edge
    {
        public int vertexA;
        public int vertexB;
        public SymmetricMatrix q;
        public Vector3d p;
        public double error;
        public bool isDeleted;
        public bool isBorder2D;
        public bool isUVSeam;

        public Edge(int va, int vb)
        {
            vertexA = va;
            vertexB = vb;
        }
    }

    /// <summary>
    /// The mesh simplifier.
    /// Deeply based on https://github.com/sp4cerat/Fast-Quadric-Mesh-Simplification but rewritten completely in C#.
    /// </summary>
    public sealed partial class MeshSimplifier
    {
        private ResizableArray<Edge> edgesRA;
        private ResizableArray<Edge> vtx2edges;
        private float RecycleRejectedEdgesThreshold;

        /// <summary>
        /// Return true if this edge can be collapsed without causing problem
        /// Also update triangles normal and list of triangles passed as references
        /// </summary>
        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private bool ValidateContractionThenUpdateTrisNormals(
            Edge edge,
            ref int survivedIndex,
            ref int deletedIndex,
            ref List<Triangle> trisTouchingSurvivedVertexOnly,
            ref List<Triangle> trisTouchingDeletedVertexOnly,
            ref List<Triangle> trisTouchingBothVertices
        )
        {
            bool edgeContractionAccepted = true;

            trisTouchingSurvivedVertexOnly.Clear();
            trisTouchingDeletedVertexOnly.Clear();
            trisTouchingBothVertices.Clear();
            List<Triangle>[] trisTouchingThisVextexOnly =
                { trisTouchingSurvivedVertexOnly, trisTouchingDeletedVertexOnly };

            if (vertices[edge.vertexA].tcount > vertices[edge.vertexB].tcount)
            {
                survivedIndex = edge.vertexA;
                deletedIndex = edge.vertexB;
            }
            else
            {
                survivedIndex = edge.vertexB;
                deletedIndex = edge.vertexA;
            }

            int[] edgeVertex = { survivedIndex, deletedIndex };

            // extract triangles touching each vertex and update normals if edge can be contracted
            Triangle t;
            Vertex v;
            Ref r;

            for (int j = 0; j < EdgeVertexCount; j++)
            {
                int notj = j == 0 ? 1 : 0;
                v = vertices[edgeVertex[j]];
                for (int i = v.tstart; i < v.tstart + v.tcount; i++)
                {
                    r = vtx2tris[i];
                    t = triangles[r.tid];
                    if (!t.deleted)
                    {
                        //int v0 = edgeVertex[j]; // v0 is also equals to t[r.tvertex] and v.index;
                        int v1 = t[(r.tvertex + 1) % TriangleEdgeCount];
                        int v2 = t[(r.tvertex + 2) % TriangleEdgeCount];

                        // test if triangle touches both edge vertices
                        if (v1 == edgeVertex[notj] || v2 == edgeVertex[notj])
                        {
                            if (!trisTouchingBothVertices.Contains(t))
                                trisTouchingBothVertices.Add(t);
                            continue;
                        }

                        // test if triangle will flip after edge contraction
                        Vector3d d1 = vertices[v1].p - edge.p;
                        d1.Normalize();
                        Vector3d d2 = vertices[v2].p - edge.p;
                        d2.Normalize();
                        Vector3d n;
                        Vector3d.Cross(ref d1, ref d2, out n);
                        n.Normalize();
                        if (Vector3d.Dot(ref n, ref t.n) < FlippedTriangleCriteria)
                        {
                            edgeContractionAccepted = false;
                            return edgeContractionAccepted;
                        }

                        // update cache
                        if (Vector3d.Dot(ref d1, ref d2) > DegeneratedTriangleCriteria)
                        {
                            edgeContractionAccepted = false;
                            return edgeContractionAccepted;
                        }
                        else
                        {
                            t.nCached = n;
                        }

                        t.refCached = r;

                        trisTouchingThisVextexOnly[j].Add(t);
                    }
                }
            }

            // update normal of all triangles that have changed
            for (int j = 0; j < EdgeVertexCount; j++)
                foreach (var tt in trisTouchingThisVextexOnly[j])
                {
                    tt.n = tt.nCached;
                }

            return edgeContractionAccepted;
        }

        [MethodImpl(MethodImplOptions.AggressiveInlining)]
        private void CalculateEdgeError(Edge edge)
        {
            const double nearZero = 1E-6;
            Vertex va = this.vertices.Data[edge.vertexA];
            Vertex vb = this.vertices.Data[edge.vertexB];
            SymmetricMatrix q = edge.q;

            q.Clear();
            q.Add(va.q);
            q.Add(vb.q);
            q.Subtract(edge.qTwice);
            if (PreserveBorderEdges || PreserveUVSeamEdges || PreserveUVFoldoverEdges)
            {
                q.Add(va.qPenaltyEdge);
                q.Add(vb.qPenaltyEdge);
            }

            edge.error = -1;
            if (q.ShapeIsGood())
            {
                // Gauss - Jordan Elimination method
                double P = q.m1 * q.m5 - q.m2 * q.m4;
                double Q = q.m1 * q.m7 - q.m2 * q.m5;
                double R = q.m1 * q.m8 - q.m2 * q.m6;
                double S = q.m0 * q.m4 - q.m1 * q.m1;
                double T = q.m0 * q.m5 - q.m1 * q.m2;
                double U = q.m0 * q.m6 - q.m1 * q.m3;
                double Zd = S * Q - P * T;

                if (((Zd > nearZero) || (Zd < -nearZero)) && ((S > nearZero) || (S < -nearZero)))
                {
                    double z = -(S * R - P * U) / Zd;
                    double y = -(U + T * z) / S; // back substitution for y
                    double x = -(q.m3 + q.m1 * y + q.m2 * z) / q.m0; // then x

                    edge.p = new Vector3d(x, y, z); // optimal solution
                    edge.error = Math.Abs(VertexError(q, edge.p.x, edge.p.y, edge.p.z));
                    //DebugMeshPerf.Data.nrErrorTypeEllipsoid++;
                }
            }

            if (edge.error == -1)
            {
                Vector3d p1 = va.p;
                Vector3d p2 = vb.p;
                Vector3d p3 = (va.p + vb.p) * 0.5;

                double error1 = Math.Abs(VertexError(q, p1.x, p1.y, p1.z));
                double error2 = Math.Abs(VertexError(q, p2.x, p2.y, p2.z));
                double error3 = Math.Abs(VertexError(q, p3.x, p3.y, p3.z));

                if (error1 < error2)
                {
                    if (error1 < error3)
                    {
                        edge.error = error1;
                        edge.p = p1;
                    }
                    else
                    {
                        edge.error = error3;
                        edge.p = p3;
                    }
                }
                else if (error2 < error3)
                {
                    edge.error = error2;
                    edge.p = p2;
                }
                else
                {
                    edge.error = error3;
                    edge.p = p3;
                }

                //DebugMeshPerf.Data.nrErrorTypeVertex++;
            }

            double curvatureError = 0;
            if (RegardCurvature)
            {
                Vertex vert0 = this.vertices[edge.vertexA];
                Vertex vert1 = this.vertices[edge.vertexB];
                curvatureError = CurvatureError(ref vert0, ref vert1);
            }

            edge.error += curvatureError;
        }

        /// <summary>
        /// Create edge objects required to build a list of edges sorted by increasing quadric errors.
        /// All triangles and vertices must have been created and initialized before calling this procedure.
        /// The procedure will create an edge object for each edge of every triangle(without duplicating edges)
        /// Note that an edge from vertex Vi to Vj and an edge from vertex Vj to Vi
        /// are the same edge.
        /// </summary>
        /// <param name="degeneratedTriangles">degenerated triangles already count as deleted triangles</param>
        private void InitEdges(out int degeneratedTriangles)
        {
            var triangles = this.triangles.Data;
            int triangleCount = this.triangles.Length;
            var vertices = this.vertices.Data;
            int verticesCount = this.vertices.Length;
            degeneratedTriangles = 0;
            Triangle t, t1, t2;
            Vertex v, vxa, vxb;
            Edge e = null;
            this.edgesRA = new ResizableArray<Edge>(triangleCount * 3);
            var edges = this.edgesRA.Data;
            int[,] edgeBorder = new int[triangleCount * 3, 3];
            int edgeCount = 0;

            // create references between vertices and edges
            {
                // init edges count estimation
                int start = 0;
                for (int i = 0; i < verticesCount; i++)
                {
                    v = vertices[i];
                    v.estart = start;
                    v.ecount = 0;
                    start += v.tcount * 2;
                }

                vtx2edges = new ResizableArray<Edge>(start * 2, start); // will consume extra memory ...

                var v2t = this.vtx2tris.Data;
                var v2e = this.vtx2edges.Data;

                // create edges, init qTwice, init border
                for (int i = 0; i < triangleCount; i++)
                {
                    t = triangles[i];
                    if (t.deleted)
                        continue;
                    // skip degenerated triangle (it happens when using smart linking on cad from external apps)
                    if ((t.v0 == t.v1) || (t.v1 == t.v2) || (t.v2 == t.v0))
                    {
                        t.deleted = true;
                        degeneratedTriangles++;
                        continue;
                    }

                    int va = t[0];
                    for (int j = 0; j < TriangleEdgeCount; j++)
                    {
                        // create or get this edge
                        int vb = t[(j + 1) % TriangleEdgeCount];
                        vxa = vertices[va];
                        vxb = vertices[vb];
                        ulong ekey = Edge.CalculateKey(va, vb);
                        bool edgeDoesNotExist = true;

                        for (int k = 0; k < vxa.ecount; k++)
                        {
                            if (v2e[vxa.estart + k].key == ekey)
                            {
                                edgeDoesNotExist = false;
                                e = v2e[vxa.estart + k];
                                break;
                            }
                        }

                        if (edgeDoesNotExist)
                        {
                            e = new Edge(va, vb);
                            e.index = edgeCount++;
                            edges[e.index] = e;
                            v2e[vxa.estart + vxa.ecount++] = e;
                            v2e[vxb.estart + vxb.ecount++] = e;
                        }

                        //
                        e.qTwice.Add(ref t.n, ref vxa.p);
                        // count tris for border detection
                        int trisCount = edgeBorder[e.index, 0];
                        edgeBorder[e.index, 0] = ++trisCount;
                        // No more than 2 triangles are required for the test
                        if (trisCount <= 2)
                            edgeBorder[e.index, trisCount] = t.index;

                        va = vb;
                    }

                    e.containingTriangle = t;
                }
            }
            this.edgesRA.Resize(edgeCount, true, false);
            edges = this.edgesRA.Data;

            // check to preserve edge
            for (int i = 0; i < edgeCount; i++)
            {
                e = edges[i];

                if (edgeBorder[i, 0] == 1) // only one triangle along this edge
                {
                    e.isBorder2D = true;
                    //DebugMeshPerf.Data.nrBorder2D++;
                }
                else if (edgeBorder[i, 0] == 2)
                {
                    t1 = triangles[edgeBorder[i, 1]];
                    t2 = triangles[edgeBorder[i, 2]];
                    if (Vector3d.Dot(ref t1.n, ref t2.n) < -0.9999) // double faced plane
                    {
                        e.isBorder2D = true;
                        //DebugMeshPerf.Data.nrBorder2D++;
                    }
                }

                if (vertices[e.vertexA].uvSeamEdge && vertices[e.vertexB].uvSeamEdge)
                {
                    e.isUVSeam = true;
                    //DebugMeshPerf.Data.nrUVSeamEdge++;
                }
                else if (vertices[e.vertexA].uvFoldoverEdge && vertices[e.vertexB].uvFoldoverEdge)
                {
                    e.isUVFoldover = true;
                    //DebugMeshPerf.Data.nrUVFoldoverEdge++;
                }

                if ((e.isBorder2D && PreserveBorderEdges) || (e.isUVSeam && PreserveUVSeamEdges) ||
                    (e.isUVFoldover && PreserveUVFoldoverEdges))
                {
                    t1 = triangles[edgeBorder[i, 1]];
                    CalculateEdgePenaltyMatrix(t1, e);
                    DistributeEdgePenaltyMatrix(e);
                }
            }

            // calculate edge error
            for (int i = 0; i < edgeCount; i++)
            {
                e = edges[i];
                CalculateEdgeError(e);
                e.errorKeyed = e.error;
            }

            // copy to sorted edges list
            this.edgesL = edges.OrderBy(ee => ee.errorKeyed).ToList();
        }

        private void RemoveEdgePass(int trisToDelete, ref int deletedTris)
        {
            var triangles = this.triangles.Data;
            var vertices = this.vertices.Data;
            var vtx2edges = this.vtx2edges.Data;
            var edgesL = this.edgesL;

            List<Edge> edgesLRejected = new List<Edge>();
            int recycleRejectedEdges = (int) (edgesL.Count * RecycleRejectedEdgesThreshold);

            List<Triangle> trisTouchingSurvivedVertexOnly = new List<Triangle>();
            List<Triangle> trisTouchingDeletedVertexOnly = new List<Triangle>();
            List<Triangle> trisTouchingBothVertices = new List<Triangle>();
            Dictionary<int, int> AttributeMapping = new Dictionary<int, int>();

            Edge edgeAssessed = null, edgeToMove = null, survivedEdge = null;
            Vertex survivedVertex, deletedVertex;
            Vector3 barycentricCoord = new Vector3();
            int survivedIndex = -1, deletedIndex = -1, thirdIndex = -1;
            int rankSurvivedIndex = -1, rankDeletedIndex = -1, rankThirdIndex = -1;

            int currentEdgeRank = 0;


            while ((trisToDelete > deletedTris) && (currentEdgeRank < edgesL.Count))
            {
                //DebugMeshPerf.Data.nrLoopTest++;

                int index = currentEdgeRank++;
                edgeAssessed = edgesL[index];

                // skip deleted edges
                if (edgeAssessed.isDeleted)
                    continue;

                // need re-sorting this edge
                if (edgeAssessed.error > edgeAssessed.errorKeyed)
                {
                    CalculateEdgeError(edgeAssessed);
                    //DebugMeshPerf.Data.nrErrorEval++; //
                    edgeAssessed.errorKeyed = edgeAssessed.error;
                    edgesL.AddSortedFromPosition(currentEdgeRank, edgeAssessed);
                    //DebugMeshPerf.Data.nrEdgeReinsert++;
                    continue;
                }

                else if (edgeAssessed.error < edgeAssessed.errorKeyed)
                {
                    //DebugMeshPerf.Data.nrEdgeLag++;
                }

                // retrieve all triangles touching this edge
                if (!ValidateContractionThenUpdateTrisNormals(
                        edgeAssessed,
                        ref survivedIndex,
                        ref deletedIndex,
                        ref trisTouchingSurvivedVertexOnly,
                        ref trisTouchingDeletedVertexOnly,
                        ref trisTouchingBothVertices
                    ))
                {
                    edgesLRejected.Add(edgeAssessed);
                    //DebugMeshPerf.Data.nrEdgeRejected++;
                    continue;
                }

                survivedVertex = vertices[survivedIndex];
                deletedVertex = vertices[deletedIndex];

                // triangles to delete
                int deletedCount = 0;
                AttributeMapping.Clear();
                foreach (var t in trisTouchingBothVertices)
                {
                    // interpolate vertex attributes of new point p on the deleted edge

                    for (int i = 0; i <= TriangleEdgeCount; i++)
                    {
                        if (t[i] == survivedIndex)
                        {
                            rankSurvivedIndex = i;
                            rankDeletedIndex = (i + 1) % TriangleEdgeCount; // guess
                            if (t[rankDeletedIndex] != deletedIndex) // verify
                                rankDeletedIndex = (i + 2) % TriangleEdgeCount;
                            rankThirdIndex = TriangleEdgeCount - rankDeletedIndex - rankSurvivedIndex;
                            thirdIndex = t[rankThirdIndex];
                            break;
                        }
                    }

                    t.GetAttributeIndices(attributeIndexArr);
                    int ia0 = attributeIndexArr[rankSurvivedIndex];
                    int ia1 = attributeIndexArr[rankDeletedIndex];
                    int ia2 = attributeIndexArr[rankThirdIndex];

                    if (!AttributeMapping.ContainsValue(ia0))
                    {
                        CalculateBarycentricCoords(
                            ref edgeAssessed.p,
                            ref survivedVertex.p,
                            ref deletedVertex.p,
                            ref vertices[thirdIndex].p,
                            out barycentricCoord
                        );
                        InterpolateVertexAttributes(ia0, ia0, ia1, ia2, ref barycentricCoord);
                        AttributeMapping[ia1] = ia0;
                    }

                    t.deleted = true;
                    deletedCount++;
                }

                // attach tris to survided vertex
                foreach (var t in trisTouchingDeletedVertexOnly)
                {
                    rankDeletedIndex = t.refCached.tvertex;
                    t[rankDeletedIndex] = survivedIndex;

                    int SurvivedAttrib;
                    if (AttributeMapping.TryGetValue(t.GetAttributeIndex(rankDeletedIndex), out SurvivedAttrib))
                        t.SetAttributeIndex(rankDeletedIndex, SurvivedAttrib);
                    trisTouchingSurvivedVertexOnly.Add(t);
                }

                // attach edges to survided vertex
                edgeAssessed.isDeleted = true;
                for (int i = 0; i < deletedVertex.ecount; i++)
                {
                    edgeToMove = vtx2edges[deletedVertex.estart + i];
                    if (!edgeToMove.isDeleted)
                    {
                        ulong dkey;
                        if (edgeToMove.vertexA == deletedIndex)
                            dkey = Edge.CalculateKey(survivedIndex, edgeToMove.vertexB);
                        else
                            dkey = Edge.CalculateKey(survivedIndex, edgeToMove.vertexA);
                        bool canAttach = true;
                        for (int j = 0; j < survivedVertex.ecount; j++)
                        {
                            if (vtx2edges[survivedVertex.estart + j].key == dkey)
                            {
                                canAttach = false;
                                survivedEdge = vtx2edges[survivedVertex.estart + j];
                                break;
                            }
                        }

                        if (canAttach)
                        {
                            edgeToMove.ReplaceVertex(deletedIndex, survivedIndex);
                        }
                        else
                        {
                            edgeToMove.isDeleted = true;
                            survivedEdge.isBorder2D |= edgeToMove.isBorder2D;
                            survivedEdge.isUVSeam |= edgeToMove.isUVSeam;
                            survivedEdge.isUVFoldover |= edgeToMove.isUVFoldover;
                        }
                    }
                }

                //
                // update references :
                //
                // 1- vertices to tris
                int tstart = this.vtx2tris.Length;
                foreach (var t in trisTouchingSurvivedVertexOnly)
                {
                    this.vtx2tris.Add(t.refCached);
                }

                int tcount = this.vtx2tris.Length - tstart;
                survivedVertex.tstart = tstart;
                survivedVertex.tcount = tcount;
                deletedVertex.tcount = 0;
                // 2- vertices to edges
                int estart = this.vtx2edges.Length;
                for (int i = 0; i < survivedVertex.ecount; i++)
                {
                    survivedEdge = this.vtx2edges[survivedVertex.estart + i];
                    if (!survivedEdge.isDeleted)
                        this.vtx2edges.Add(survivedEdge);
                }

                for (int i = 0; i < deletedVertex.ecount; i++)
                {
                    survivedEdge = this.vtx2edges[deletedVertex.estart + i];
                    if (!survivedEdge.isDeleted)
                        this.vtx2edges.Add(survivedEdge);
                }

                int ecount = this.vtx2edges.Length - estart;
                survivedVertex.estart = estart;
                survivedVertex.ecount = ecount;
                deletedVertex.ecount = 0;
                vtx2edges = this.vtx2edges.Data;

                survivedVertex.p = edgeAssessed.p;

                // Update the matrices and error on the edges around survived vertex
                //  step 1 - update quadrics error matrice Q at vertex V0 and at every vertex V1 connected to V0.
                //           Also border penalty matrices calculated on the edges need to be propagated to vertices.
                //  setp 2 - calculate edges error E and optimal vertex position p on all edges touching V0 and V1
                {
                    Triangle t0, t1;
                    Vertex v0, v1;
                    Edge e0, e1;

                    // step 1 : update quadrics matrices
                    // 1a) reset all matrices
                    v0 = survivedVertex;
                    v0.q.Clear();
                    v0.qPenaltyEdge.Clear();

                    for (int i = 0; i < v0.ecount; i++)
                    {
                        e0 = vtx2edges[v0.estart + i];
                        // vertex at opposite end
                        if (e0.vertexA == v0.index)
                            v1 = vertices[e0.vertexB];
                        else
                            v1 = vertices[e0.vertexA];
                        v1.q.Clear();
                        v1.qPenaltyEdge.Clear();

                        for (int j = 0; j < v1.ecount; j++)
                        {
                            e1 = vtx2edges[v1.estart + j]; // note that one of the e1 is also e0
                            e1.qTwice.Clear();
                            e1.flagCalculateQstate = Edge.QState.QIsNotCalculated;
                        }
                    }

                    // 1b) Calculate quadrics matrices
                    for (int i = 0; i < v0.ecount; i++)
                    {
                        e0 = vtx2edges[v0.estart + i];
                        // vertex at opposite end
                        if (e0.vertexA == v0.index)
                            v1 = vertices[e0.vertexB];
                        else
                            v1 = vertices[e0.vertexA];

                        for (int j = 0; j < v1.ecount; j++)
                        {
                            e1 = vtx2edges[v1.estart + j]; // note that one of the e1 is also e0
                            for (int k = 0; k < v1.tcount; k++)
                            {
                                t1 = triangles[vtx2tris[v1.tstart + k].tid];
                                if (t1.deleted)
                                    continue;
                                if (e1.flagCalculateQstate != Edge.QState.QIsCalculated)
                                {
                                    // is e1 an edge of triangle t1 ?
                                    if (((e1.vertexA == t1.v0) || (e1.vertexA == t1.v1) || (e1.vertexA == t1.v2))
                                        && ((e1.vertexB == t1.v0) || (e1.vertexB == t1.v1) || (e1.vertexB == t1.v2)))
                                    {
                                        e1.qTwice.Add(ref t1.n, ref v1.p);
                                        // if e1 is an edge and it has not been evaluated then do it
                                        if (((e1.isBorder2D && PreserveBorderEdges) ||
                                                (e1.isUVSeam && PreserveUVSeamEdges) ||
                                                (e1.isUVFoldover && PreserveUVFoldoverEdges))
                                            && (e1.flagCalculateQstate == Edge.QState.QIsNotCalculated))
                                        {
                                            CalculateEdgePenaltyMatrix(t1, e1);
                                            e1.flagCalculateQstate = Edge.QState.QPenaltyIsCalculated;
                                        }
                                    }
                                }

                                v1.q.Add(ref t1.n, ref v1.p);
                            }

                            if ((e1.isBorder2D && PreserveBorderEdges) || (e1.isUVSeam && PreserveUVSeamEdges) ||
                                (e1.isUVFoldover && PreserveUVFoldoverEdges))
                                DistributeEdgePenaltyMatrix(e1, v1);
                            e1.flagCalculateQstate = Edge.QState.QIsCalculated;
                        }

                        if ((e0.isBorder2D && PreserveBorderEdges) || (e0.isUVSeam && PreserveUVSeamEdges) ||
                            (e0.isUVFoldover && PreserveUVFoldoverEdges))
                            DistributeEdgePenaltyMatrix(e0, v0);
                    }

                    for (int k = 0; k < v0.tcount; k++)
                    {
                        t0 = triangles[vtx2tris[v0.tstart + k].tid];
                        if (t0.deleted)
                            continue;
                        v0.q.Add(ref t0.n, ref v0.p);
                    }

                    // step 2 : update error
                    //// Note:
                    //// finally I will not update edge error beyond edge connected to vertex v0 for now because I have observed that:
                    //// 1- it reduces the execution time and
                    //// 2- the accuracy is better if I recalculate the edge error at the beginning of the main loop
                    for (int i = 0; i < v0.ecount; i++)
                    {
                        e0 = vtx2edges[v0.estart + i];
                        if (e0.flagCalculateQstate != Edge.QState.ErrorIsCalculated)
                        {
                            CalculateEdgeError(e0);
                            //DebugMeshPerf.Data.nrErrorEval++;
                            e0.flagCalculateQstate = Edge.QState.ErrorIsCalculated;
                        }
                    }
                }

                // try to collapse previously rejected edges. This improves quality for high reduction and low tris mesh
                if (edgesLRejected.Count >= recycleRejectedEdges)
                {
                    for (int i = 0; i < edgesLRejected.Count; i++)
                    {
                        edgeToMove = edgesLRejected[i];
                        if (!edgeToMove.isDeleted)
                        {
                            CalculateEdgeError(edgeToMove);
                            edgeToMove.errorKeyed = edgeToMove.error;
                            edgesL.AddSortedFromPosition(currentEdgeRank, edgeToMove);
                            //DebugMeshPerf.Data.nrEdgeReinsert++;
                            //DebugMeshPerf.Data.nrEdgeRejected--;
                        }
                    }

                    edgesLRejected.Clear();
                    recycleRejectedEdges +=
                        (int) ((edgesL.Count - currentEdgeRank) *
                            RecycleRejectedEdgesThreshold); // slow down rate to avoid stalling the algorithm; could be improved !
                }


                deletedTris += deletedCount;
                //DebugMeshPerf.Data.nrLoopComplete++;
            }
        }

        /// <summary>
        /// Simplifies the mesh to a desired quality.
        /// </summary>
        /// <param name="quality">The target quality (between 0 and 1).</param>
        private void SimplifyMeshByEdge(float quality)
        {
            quality = Mathf.Clamp01(quality);

            int deletedTris = 0;
            var triangles = this.triangles.Data;
            int triangleCount = this.triangles.Length;
            int trisToDelete = (int) (triangleCount * (1.0f - quality));

            //DebugMeshPerf.Data.Reset();

            UpdateMesh(0);
            InitEdges(out deletedTris);
            RemoveEdgePass(trisToDelete, ref deletedTris);


            if (trisToDelete > deletedTris)
            {
                //Debug.Log("Unable to delete the specified number of triangles");
            }

            CompactMesh();

            if (verbose)
            {
                //DebugMeshPerf.Data.nrTrisBefore = triangleCount;
                //DebugMeshPerf.Data.nrTrisAfter = triangleCount - deletedTris;
                //Debug.Log(DebugMeshPerf.Data);
            }
        }
    }
}
