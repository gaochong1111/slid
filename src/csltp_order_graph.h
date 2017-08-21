#ifndef CSLTP_ORDER_GRAPH_H
#define CSLTP_ORDER_GRAPH_H

#include<set>
#include<vector>
#include<string>

using namespace std;

class Vertex
{
public:
        Vertex();
        Vertex(string name);

        string getName();

        Vertex& operator=(const Vertex& vertex);
        bool operator < (const Vertex& vertex) const;
        bool operator == (const Vertex vertex) const;
        friend ostream& operator << (ostream& os, Vertex& vertex);
private:
        string name;
};

enum LabelOp{
        LABEL_LT=0,
        LABEL_LE
};


class Edge
{
public:
        Edge(Vertex v1, LabelOp lb ,Vertex v2);
        bool operator < (const Edge& edge) const;
        bool operator == (const Edge vertex) const;
        Vertex getSource();
        Vertex getDest() ;
        LabelOp getLabel() ;

        friend ostream& operator << (ostream& os, Edge& edge) ;

private:
        Vertex source;
        Vertex dest;
        LabelOp label;
};


// override the operator ==
bool operator == (const set<Edge>& s1, const set<Edge>& s2);
bool operator == (const set<Vertex>& s1, const set<Vertex>& s2);
// find the position of v in vec
int find_vertex(const vector<Vertex>& vec, const Vertex& v);




class OrderGraph
{
public:
        void addVertex(Vertex v) ;

        /***
         *
         * @return: 1 if ok,
         *         0 if the vertex does not exist in vertex set
         */
        int addEdge(Edge edge) ;


        /**
         * saturate the graph
         */
        void saturate() ;


        /**
         * check the order graph is consistent or inconsistent after saturating
         * @return true, if edges do not include (V,<,V)
         *         false, otherwise
         */
        bool isConsistent() ;

        /**
         * @param old_v : the old_v as vertex set
         * @param new_v : the new_v as new vertexes which may has the same element.
         * @return 1, if ok
         *         -1, otherwise
         */
        int substitution(const vector<Vertex>& old_v, const vector<Vertex>& new_v) ;


        /**
         * union graph og into this, vertexes union og.vertexes, edges union og.edges
         * @param og : union graph
         */
        void unionGraph(const OrderGraph& og) ;

        /**
         * restrict the order graph in vertex set
         * @param v_set : the restriction set
         * @return 1, if okay
         *        -1, otherwise
         */
        int restriction(set<Vertex>& v_set) ;


        bool operator == (const OrderGraph& og) const ;

        set<Vertex> getVertexes();
        set<Edge> getEdges();

        void printAsDot(string file) ;
private:
        void delSpecialChar(string& str); // process the vertex name , used by printasdot

private:
        set<Vertex> vertexes;
        set<Edge> edges;
};


class OrderGraphSet
{
public:
        /**
         * if og does not exist then  insert it.
         * @params og
         */
        void addOrderGraph(OrderGraph og) ;

        bool isExist(const OrderGraph& og) const;

        int size() ;

        OrderGraph at(unsigned int i) ;

        bool operator == (const OrderGraphSet& ogset) const;

private:
        vector<OrderGraph> graphs;
};

#endif // csltp_order_graph.h
