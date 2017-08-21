#include<iostream>
#include<fstream>
#include<locale>
#include "csltp_order_graph.h"

/** class Vertex  **/
Vertex::Vertex(){}

Vertex::Vertex(string name) {
        this->name = name;
}

string Vertex::getName(){
        return this->name;
}

Vertex& Vertex::operator= (const Vertex& vertex) {
        this->name = vertex.name;
        return *this;
}

bool Vertex:: operator< (const Vertex& vertex) const{
        return this->name < vertex.name;
}
bool Vertex:: operator == (const Vertex vertex) const {
        // cout<< "in Vertex: override == \n";
        return this->name == vertex.name;
}

ostream& operator << (ostream& os, Vertex& vertex) {
        os<<vertex.name;
        return os;
}

/** class Edge **/

Edge::Edge(Vertex v1, LabelOp lb ,Vertex v2) {
        this->source = v1;
        this->label = lb;
        this->dest = v2;
}

bool Edge::operator < (const Edge& edge) const {
        if (this->source < edge.source ||
            (edge.source == this->source && this->label < edge.label) ||
            (edge.source == this->source && this->label == edge.label && this->dest < edge.dest)) {
                return true;
        }

        return false;
}

bool Edge::operator == (const Edge edge) const {
        cout<< "in Edge: override == \n";
        return this->label== edge.label && this->source == edge.source && this->dest == edge.dest;
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
        for (unsigned int i=0; i<vec.size(); i++) {
                if (vec[i] == v) {
                        return i;
                }
        }
        return -1;
}


/** class OrderGraph **/

void OrderGraph::addVertex(Vertex v) {
        if (this->vertexes.find(v) == this->vertexes.end()) {
                this->vertexes.insert(v);
                locale loc;
                string name = v.getName();
                if (isdigit(name[0], loc)) {
                        for (auto vertex : this->vertexes) {
                                if(vertex == v) continue;

                                string dest = vertex.getName();
                                int name_i = atoi(name.c_str());
                                if(isdigit(dest[0], loc)) {
                                        int dest_i = atoi(dest.c_str());
                                        if (dest_i < name_i) {
                                                Edge e_lt(vertex, LABEL_LT, v);
                                                edges.insert(e_lt);
                                        } else {
                                                Edge e_gt(v, LABEL_LT, vertex);
                                                edges.insert(e_gt);
                                        }
                                }
                        }
                }
        }
}

/***
 *
 * @return: 1 if ok,
 *         0 if the vertex does not exist in vertex set
 */
int OrderGraph::addEdge(Edge edge) {
        if (this->vertexes.find(edge.getSource()) != this->vertexes.end() &&
            this->vertexes.find(edge.getDest()) != this->vertexes.end()) {
                // Vertex v_s = edge.getSource();
                // Vertex v_d = edge.getDest();
                bool res = (edge.getSource() == edge.getDest());
                // cout << v_s  << " --- " << v_d << " == : "<< res << endl;
                if (res && edge.getLabel() == LABEL_LE) {
                        // V <= V, do not insert
                        // cout << "do nothing .\n";
                        return 1;
                }
                edges.insert(edge);
                return 1;
        }

        locale loc;
        string source = edge.getSource().getName();
        string dest = edge.getDest().getName();
        bool is_source = isdigit(source[0], loc);
        bool is_dest = isdigit(dest[0], loc);
        if (is_source || is_dest) {
                if (is_source) {
                        this->addVertex(edge.getSource());
                }
                if (is_dest) {
                        this->addVertex(edge.getDest());
                }
                edges.insert(edge);
                return 1;
        }

        return 0;
}

set<Vertex> OrderGraph::getVertexes() {
        return this->vertexes;
}

set<Edge> OrderGraph::getEdges() {
        return this->edges;
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
                                                // this->edges.insert(edge);
                                                this->addEdge(edge);
                                        } else {
                                                Edge edge(edge1.getSource(), LABEL_LT, edge2.getDest());
                                                // this->edges.insert(edge);
                                                this->addEdge(edge);
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
        for (unsigned int i=0; i<old_v.size(); i++) {
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
        for (unsigned int i=0; i<new_v.size(); i++) {
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

                        // this->edges.insert(e);
                        this->addEdge(e);
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
                // this->vertexes.insert(vertex);
                this->addVertex(vertex);
        }
        for (auto edge : og.edges) {
                // this->edges.insert(edge);
                this->addEdge(edge);
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
                        locale loc;
                        string source = edge.getSource().getName();
                        bool is_source = isdigit(source[0], loc);
                        string dest = edge.getDest().getName();
                        bool is_dest = isdigit(dest[0], loc);
                        if(!is_source && !is_dest) {
                                this->edges.erase(edge);
                        }
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

/**
 * print as dot file
 * @param file: file path
 */
void OrderGraph::printAsDot(string file) {

        string label_str[] = {"<", "<="}; //used by print label

        ofstream fs(file);
        if (!fs) return;
        fs<<"digraph{\n";
        for (auto vertex : vertexes) {
                string vertex_name = vertex.getName();
                this->delSpecialChar(vertex_name);
                fs << vertex_name<<";\n";
        }
        for (auto edge : edges) {
                // if (edge.getSource() == edge.getDest() && edge.getLabel()==LABEL_LE)
                //        continue;
                string source_name = edge.getSource().getName();
                string dest_name  = edge.getDest().getName();
                // cout << source_name << "->" << dest_name <<endl;

                this->delSpecialChar(source_name);
                this->delSpecialChar(dest_name);
                fs << source_name << "->" <<dest_name<<"[label=\""<<label_str[edge.getLabel()] <<"\"];\n";
        }
        fs<<"}\n";
        fs.close();
}

void OrderGraph::delSpecialChar(string& str) {
        string::iterator it;
        for(it=str.begin(); it != str.end(); it++) {
                if ((*it >= '!' && *it <= '.') ||
                    (*it >= '<' && *it <= '?')) {
                        str.erase(it);
                }
        }
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

bool OrderGraphSet::isExist(const OrderGraph& og) const{

        for (unsigned int i=0; i < this->graphs.size(); i++) {
                if (this->graphs[i] == og) {
                        return true;
                }
        }
        return false;
}

int OrderGraphSet::size() {
        return this->graphs.size();
}

OrderGraph OrderGraphSet::at(unsigned int i) {
        if (i<this->graphs.size()) {
                return this->graphs[i];
        }
        OrderGraph og;
        return og;
}

bool OrderGraphSet::operator==(const OrderGraphSet& ogset) const {
        if (this->graphs.size() == ogset.graphs.size()) {
                for (auto graph : this->graphs) {
                        if (!ogset.isExist(graph)) {
                                return false;
                        }
                }
                return true;
        }
        return false;
}
