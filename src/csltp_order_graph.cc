#include<iostream>
#include<fstream>
#include "csltp_order_graph.h"

/** class Vertex  **/
Vertex::Vertex(string name): name(name) {}

string Vertex::getName(){
        return this->name;
}

bool Vertex:: operator< (const Vertex& vertex) const{
        return this->name < vertex.name;
}
bool Vertex:: operator == (const Vertex& vertex) const {
        return this->name == vertex.name;
}

ostream& operator << (ostream& os, Vertex& vertex) {
        os<<vertex.name;
        return os;
}

/** class Edge **/

Edge::Edge(Vertex v1, LabelOp lb ,Vertex v2) :source(v1),label(lb) ,dest(v2){
}

bool Edge::operator < (const Edge& edge) const {
        if (this->source < edge.source ||
            (edge.source == this->source && this->label < edge.label) ||
            (edge.source == this->source && this->label == edge.label && this->dest < edge.dest)) {
                return true;
        }

        return false;
}

Vertex Edge::getSource() {
        return this->source;
}

Vertex Edge::getDest() {
        return this->dest;
}

LabelOp Edge::getLabel() {
        return this->label;
}

ostream& operator << (ostream& os, Edge& edge) {
        os << edge.source << "--" << edge.label <<"-->" << edge.dest;
        return os;
}

/** global function  **/
bool operator == (const set<Edge>& s1, const set<Edge>& s2) {
        if(s1.size() == s2.size()) {
                for (auto edge : s1) {
                        if (s2.find(edge) == s2.end()) {
                                return false;
                        }
                }
                return true;
        }
        return false;
}

bool operator == (const set<Vertex>& s1, const set<Vertex>& s2) {
        if(s1.size() == s2.size()) {
                for (auto edge : s1) {
                        if (s2.find(edge) == s2.end()) {
                                return false;
                        }
                }
                return true;
        }
        return false;
}

int find_vertex(const vector<Vertex>& vec, const Vertex& v) {
        for (int i=0; i<vec.size(); i++) {
                if (vec[i] == v) {
                        return i;
                }
        }
        return -1;
}


/** class OrderGraph **/

void OrderGraph::addVertex(Vertex v) {
        this->vertexes.insert(v);
}

/***
 *
 * @return: 1 if ok,
 *         0 if the vertex does not exist in vertex set
 */
int OrderGraph::addEdge(Edge edge) {
        if (this->vertexes.find(edge.getSource()) != this->vertexes.end() &&
            this->vertexes.find(edge.getDest()) != this->vertexes.end()) {
                edges.insert(edge);
                return 1;
        }
        return 0;
}


/**
 * saturate the graph
 */
void OrderGraph::saturate() {

        set<Edge> new_edges;

        int size = this->edges.size();

        while(new_edges != this->edges) {
                new_edges = this->edges;
                for (auto edge1 : new_edges) {
                        for (auto edge2 : new_edges) {
                                if (edge1.getDest() == edge2.getSource()) {
                                        if (edge1.getLabel() == LABEL_LE && edge2.getLabel() == LABEL_LE ) {
                                                Edge edge(edge1.getSource(), LABEL_LE, edge2.getDest());
                                                this->edges.insert(edge);
                                        } else {
                                                Edge edge(edge1.getSource(), LABEL_LT, edge2.getDest());
                                                this->edges.insert(edge);
                                        }
                                }
                        }
                }
        }
}


/**
 * check the order graph is consistent or inconsistent after saturating
 * @return true, if edges do not include (V,<,V)
 *         false, otherwise
 */
bool OrderGraph::isConsistent() {
        for (auto edge : this->edges) {
                if (edge.getSource() == edge.getDest() && edge.getLabel()==LABEL_LT) {
                        return false;
                }
        }
        return true;
}

/**
 * @param old_v : the old_v as vertex set
 * @param new_v : the new_v as new vertexes which may has the same element.
 * @return 1, if ok
 *         -1, otherwise
 */
int OrderGraph::substitution(const vector<Vertex>& old_v, const vector<Vertex>& new_v) {
        if (old_v.size() != new_v.size())
                return -1; // error

        set<Vertex> old_vertexes;
        for (int i=0; i<old_v.size(); i++) {
                old_vertexes.insert(old_v[i]);
                // substitute vertex
                // erase old
                if (this->vertexes.find(old_v[i]) != this->vertexes.end()) {
                        this->vertexes.erase(old_v[i]);
                } else {
                        return -1;
                }
        }
        if (old_vertexes.size() != old_v.size())
                return -1;
        // insert new
        for (int i=0; i<new_v.size(); i++) {
                this->vertexes.insert(new_v[i]);
        }

        set<Edge> old_edges = this->edges;
        // substitute edges
        for (auto edge : old_edges) {
                Vertex source = edge.getSource();
                Vertex dest = edge.getDest();
                bool flag = false; // substitute flag
                if (old_vertexes.find(edge.getSource()) != old_vertexes.end()) {
                        // substitute source
                        source = new_v[find_vertex(old_v, edge.getSource())];
                        flag = true;
                }

                if (old_vertexes.find(edge.getDest()) != old_vertexes.end()) {
                        // substitute dest
                        dest = new_v[find_vertex(old_v, edge.getDest())];
                        flag = true;
                }

                if (flag) {
                        Edge e(source, edge.getLabel(), dest);
                        this->edges.erase(edge);
                        this->edges.insert(e);
                }
        }
        return 1;
}


/**
 * union graph og into this, vertexes union og.vertexes, edges union og.edges
 * @param og : union graph
 */
void OrderGraph::unionGraph(const OrderGraph& og) {
        for (auto vertex : og.vertexes) {
                this->vertexes.insert(vertex);
        }
        for (auto edge : og.edges) {
                this->edges.insert(edge);
        }
}

/**
 * restrict the order graph in vertex set
 * @param v_set : the restriction set
 * @return 1, if okay
 *        -1, otherwise
 */
int OrderGraph::restriction(set<Vertex>& v_set) {
        for (auto vertex : v_set) {
                if (this->vertexes.find(vertex) == this->vertexes.end()) {
                        return -1;
                }
        }
        this->vertexes = v_set;
        set<Edge> edges_copy = this->edges;
        for (auto edge : edges_copy) {
                if (v_set.find(edge.getSource()) == v_set.end() ||
                    v_set.find(edge.getDest()) == v_set.end()) {
                        this->edges.erase(edge);
                }
        }
        return 1;
}


bool OrderGraph::operator == (const OrderGraph& og) const {
        if (this->vertexes == og.vertexes && this->edges == og.edges) {
                return true;
        }
        return false;
}

void OrderGraph::printAsDot(string file) {
        ofstream fs(file);
        if (!fs) return;
        fs<<"digraph{\n";
        for (auto vertex : vertexes) {
                fs << vertex.getName()<<";\n";
        }
        for (auto edge : edges) {
                if (edge.getSource() == edge.getDest() && edge.getLabel()==LABEL_LE)
                        continue;
                fs << edge.getSource().getName() << "->" <<edge.getDest().getName()<<"[label=\""<<label_str[edge.getLabel()] <<"\"];\n";
        }
        fs<<"}\n";
        fs.close();
}

/** class OrderGraphSet **/

/**
 * if og does not exist then  insert it.
 * @params og
 */
void OrderGraphSet::addOrderGraph(OrderGraph og) {
        if (!isExist(og)) {
                this->graphs.push_back(og);
        }
}

bool OrderGraphSet::isExist(const OrderGraph& og) {

        for (int i=0; i < this->graphs.size(); i++) {
                if (this->graphs[i] == og) {
                        return true;
                }
        }
        return false;
}

int OrderGraphSet::size() {
        return this->graphs.size();
}

OrderGraph OrderGraphSet::at(int i) {
        if (i>=0 && i<this->graphs.size()) {
                return this->graphs[i];
        }
        OrderGraph og;
        return og;
}
