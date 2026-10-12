import javax.swing.*;
import javax.swing.table.DefaultTableModel;
import java.awt.*;
import java.awt.event.*;
import java.io.*;
import java.util.*;
import java.util.List;

/* ===== Data structures & algorithm (no GUI dependency) ===== */
class Loc { String id, name; int x, y; Loc(String i, String n, int x, int y){id=i;name=n;this.x=x;this.y=y;} public String toString(){return name;} }
class Road { String a, b; double d, t; boolean ow; Road(String a,String b,double d,double t,boolean ow){this.a=a;this.b=b;this.d=d;this.t=t;this.ow=ow;} }
class Edge { String to; double d, t; Road r; Edge(String to,double d,double t,Road r){this.to=to;this.d=d;this.t=t;this.r=r;} }
class Entry { double k; String v; Entry(double k,String v){this.k=k;this.v=v;} }

/** Binary min-heap stored in an ArrayList. push/pop are O(log n). */
class MinHeap {
    final ArrayList<Entry> a = new ArrayList<>();
    int size(){ return a.size(); }
    void push(double k, String v){ a.add(new Entry(k,v)); int i=a.size()-1;
        while(i>0){ int p=(i-1)/2; if(a.get(p).k<=a.get(i).k) break; Collections.swap(a,p,i); i=p; } }
    Entry pop(){ Entry top=a.get(0), last=a.remove(a.size()-1);
        if(!a.isEmpty()){ a.set(0,last); int i=0;
            for(;;){ int l=2*i+1, r=l+1, m=i;
                if(l<a.size() && a.get(l).k<a.get(m).k) m=l;
                if(r<a.size() && a.get(r).k<a.get(m).k) m=r;
                if(m==i) break; Collections.swap(a,m,i); i=m; } }
        return top; }
}
class Step { String cur, msg; String[] edge; Map<String,Double> dist; Map<String,String> prev; List<String> heap; Set<String> vis; }
class Res { Map<String,Double> dist=new LinkedHashMap<>(); Map<String,String> prev=new HashMap<>(); List<Step> steps=new ArrayList<>(); }
class Info { List<String> path; List<Object[]> segs=new ArrayList<>(); double km, min, tot; }
class Route { String err; Info main, alt; boolean time; }

class Core {
    static final double INF = Double.POSITIVE_INFINITY;
    List<Loc> locs=new ArrayList<>(); List<Road> roads=new ArrayList<>(); List<String[]> deliv=new ArrayList<>(); double fuel=8;
    Core(){ reset(); }
    void reset(){
        locs.clear(); roads.clear(); deliv.clear();
        Object[][] L={{"hub","Bachupally Hub",90,110},{"pra","Pragathi Nagar",290,70},{"niz","Nizampet",220,200},{"miy","Miyapur",140,340},{"kph","KPHB",400,240},{"kuk","Kukatpally",540,110},{"jnt","JNTU",430,400},{"hit","HITEC City",650,350},{"moo","Moosapet",730,120},{"mad","Madhapur",810,250},{"gac","Gachibowli",760,500},{"lin","Lingampally",300,520}};
        for(Object[] o:L) locs.add(new Loc((String)o[0],(String)o[1],(Integer)o[2],(Integer)o[3]));
        Object[][] R={{"hub","niz",3.2,9},{"hub","pra",3.5,10},{"pra","kuk",5.1,14},{"niz","kph",4.0,12},{"niz","miy",3.8,11},{"hub","miy",5.5,15},{"miy","lin",8.2,22},{"miy","jnt",6.4,18},{"kph","kuk",3.6,11},{"kph","jnt",3.3,10},{"kuk","moo",4.2,12},{"jnt","hit",5.0,15},{"kuk","hit",6.8,20},{"moo","mad",6.0,17,true},{"hit","mad",3.4,10},{"hit","gac",4.5,13},{"lin","gac",9.5,26},{"lin","jnt",7.0,20}};
        for(Object[] o:R) roads.add(new Road((String)o[0],(String)o[1],((Number)o[2]).doubleValue(),((Number)o[3]).doubleValue(),o.length>4));
        String[][] D={{"ORD-101","Ravi Kumar","hub","mad","Anil","Delivered"},{"ORD-102","Sneha Reddy","hub","gac","Suresh","In Transit"},{"ORD-103","Farhan Ali","hub","miy","Anil","Pending"},{"ORD-104","Lakshmi P","hub","kuk","Priya","Delivered"},{"ORD-105","Karthik S","hub","lin","Suresh","Pending"},{"ORD-106","Divya N","hub","jnt","Priya","In Transit"}};
        deliv.addAll(Arrays.asList(D));
    }
    Loc loc(String id){ for(Loc l:locs) if(l.id.equals(id)) return l; return null; }
    String nm(String id){ Loc l=loc(id); return l==null?id:l.name; }
    static String f(double v){ return v==INF?"∞":String.format("%.1f",v); }

    /** Adjacency list: two-way roads add an edge in each direction, one-way roads only a→b. */
    Map<String,List<Edge>> adj(){
        Map<String,List<Edge>> m=new HashMap<>(); for(Loc l:locs) m.put(l.id,new ArrayList<>());
        for(Road r:roads){ if(!m.containsKey(r.a)||!m.containsKey(r.b)) continue;
            m.get(r.a).add(new Edge(r.b,r.d,r.t,r)); if(!r.ow) m.get(r.b).add(new Edge(r.a,r.d,r.t,r)); }
        return m; }

    private void snap(Res r,MinHeap H,Set<String> vis,String cur,String[] edge,String msg){
        Step s=new Step(); s.cur=cur; s.edge=edge; s.msg=msg; s.dist=new LinkedHashMap<>(r.dist); s.prev=new HashMap<>(r.prev);
        s.vis=new LinkedHashSet<>(vis); s.heap=new ArrayList<>(); for(Entry e:H.a) s.heap.add("("+f(e.k)+", "+nm(e.v)+")"); r.steps.add(s); }

    /** Dijkstra with a binary min-heap (lazy deletion). record=true stores snapshots for the visualiser. ban = road to ignore. */
    Res dijkstra(String src,boolean time,boolean record,Road ban){
        Res r=new Res(); Map<String,List<Edge>> adj=adj(); for(Loc l:locs) r.dist.put(l.id,INF);
        if(!adj.containsKey(src)) return r;
        MinHeap H=new MinHeap(); Set<String> vis=new LinkedHashSet<>(); r.dist.put(src,0.0); H.push(0,src);
        if(record) snap(r,H,vis,src,null,"Initialise: distance to "+nm(src)+" = 0, all others = ∞. Push (0, "+nm(src)+") into the min-heap.");
        while(H.size()>0){
            Entry e=H.pop(); String u=e.v; if(vis.contains(u)||e.k>r.dist.get(u)) continue; vis.add(u);
            if(record) snap(r,H,vis,u,null,"Extract-min: "+nm(u)+" with distance "+f(e.k)+" is now finalised (visited).");
            for(Edge ed:adj.get(u)){
                if(ed.r==ban||vis.contains(ed.to)) continue;
                double w=time?ed.t:ed.d, nd=e.k+w, old=r.dist.get(ed.to); boolean ok=nd<old;
                if(ok){ r.dist.put(ed.to,nd); r.prev.put(ed.to,u); H.push(nd,ed.to); }
                if(record) snap(r,H,vis,u,new String[]{u,ed.to},"Edge "+nm(u)+" → "+nm(ed.to)+" ("+f(w)+"): "+f(e.k)+" + "+f(w)+" = "+f(nd)+
                    (ok?" < "+f(old)+" → relax: update distance, predecessor = "+nm(u)+", push to heap.":" ≥ "+f(old)+" → no improvement."));
            } }
        if(record) snap(r,H,vis,null,null,"Heap is empty — finished. Unreachable nodes keep distance ∞.");
        return r; }

    List<String> pathOf(Res r,String s,String d){
        Double x=r.dist.get(d); if(x==null||x==INF) return null;
        LinkedList<String> p=new LinkedList<>(); p.add(d);
        while(!p.getFirst().equals(s)){ String q=r.prev.get(p.getFirst()); if(q==null) return null; p.addFirst(q); }
        return p; }

    Info info(List<String> p,boolean time){
        Map<String,List<Edge>> adj=adj(); Info in=new Info(); in.path=p;
        for(int i=1;i<p.size();i++){ String u=p.get(i-1),v=p.get(i); Edge best=null;
            for(Edge e:adj.get(u)) if(e.to.equals(v)&&(best==null||(time?e.t<best.t:e.d<best.d))) best=e;
            in.segs.add(new Object[]{u,v,best.d,best.t,best.r}); in.km+=best.d; in.min+=best.t; }
        in.tot=time?in.min:in.km; return in; }

    Route compute(String s,String d,boolean time){
        Route rt=new Route(); rt.time=time;
        if(loc(s)==null||loc(d)==null){ rt.err="Choose valid source and destination."; return rt; }
        if(s.equals(d)){ rt.err="Source and destination are the same — distance is 0."; return rt; }
        List<String> p=pathOf(dijkstra(s,time,false,null),s,d);
        if(p==null){ rt.err="No route exists from "+nm(s)+" to "+nm(d)+" (disconnected or blocked by one-way roads)."; return rt; }
        rt.main=info(p,time);
        for(Object[] sg:rt.main.segs){ List<String> p2=pathOf(dijkstra(s,time,false,(Road)sg[4]),s,d);
            if(p2!=null){ Info i2=info(p2,time); if(rt.alt==null||i2.tot<rt.alt.tot) rt.alt=i2; } }
        return rt; }

    String describe(Route rt){
        if(rt.err!=null) return "⚠ "+rt.err;
        StringBuilder sb=new StringBuilder(); Info m=rt.main;
        sb.append("Route: "); for(int i=0;i<m.path.size();i++) sb.append(i>0?" → ":"").append(nm(m.path.get(i))); sb.append("\n\n");
        int i=1; for(Object[] s:m.segs) sb.append(String.format("%2d. %s → %s   %.1f km   %.1f min%n",i++,nm((String)s[0]),nm((String)s[1]),(Double)s[2],(Double)s[3]));
        sb.append(String.format("%nTotal: %.1f km | %.1f min | fuel %.2f L (assumed %.1f L/100km)%n",m.km,m.min,m.km*fuel/100,fuel));
        if(rt.alt!=null){ sb.append(String.format("%nAlternative (best route avoiding one road of the shortest path): %.1f km, %.1f min (+%.1f %s)%n  ",rt.alt.km,rt.alt.min,rt.alt.tot-m.tot,rt.time?"min":"km"));
            for(int k=0;k<rt.alt.path.size();k++) sb.append(k>0?" → ":"").append(nm(rt.alt.path.get(k))); sb.append('\n'); }
        else sb.append("\nNo alternative route exists.\n");
        return sb.toString(); }

    /** Console self-test: run `java DeliveryRouteOptimizer --test`. */
    static void selfTest(){
        Core c=new Core(); Route r=c.compute("hub","gac",false); System.out.print(c.describe(r));
        Route t=c.compute("hub","mad",true); System.out.print("\n"+c.describe(t));
        System.out.println("\nhub→hub: "+c.compute("hub","hub",false).err);
        c.roads.removeIf(x->x.a.equals("lin")||x.b.equals("lin")); System.out.println("Isolated node: "+c.compute("hub","lin",false).err);
    }
}

/* ===== Map component ===== */
class MapPanel extends JPanel {
    final Core C; final JLabel info=new JLabel(" Click a marker or road for details");
    List<List<String>> paths=new ArrayList<>(); Set<String> vis=new HashSet<>(); String cur; String[] edge; Map<String,Double> dist; boolean labels;
    MapPanel(Core c){ C=c; setPreferredSize(new Dimension(560,380)); setBackground(DeliveryRouteOptimizer.BG);
        addMouseListener(new MouseAdapter(){ public void mousePressed(MouseEvent e){ click(e.getX(),e.getY()); } }); }
    double sx(){ return getWidth()/900.0; } double sy(){ return getHeight()/600.0; }
    void click(int px,int py){
        for(Loc l:C.locs) if(Math.hypot(l.x*sx()-px,l.y*sy()-py)<14){ info.setText(" 📍 "+l.name+"  (ID "+l.id+")"); return; }
        for(Road r:C.roads){ Loc a=C.loc(r.a),b=C.loc(r.b); if(a==null||b==null) continue;
            if(java.awt.geom.Line2D.ptSegDist(a.x*sx(),a.y*sy(),b.x*sx(),b.y*sy(),px,py)<7){ info.setText(String.format(" 🛣 %s %s %s: %.1f km, %.1f min (illustrative)",a.name,r.ow?"→":"↔",b.name,r.d,r.t)); return; } } }
    protected void paintComponent(Graphics g0){
        super.paintComponent(g0); Graphics2D g=(Graphics2D)g0; g.setRenderingHint(RenderingHints.KEY_ANTIALIASING,RenderingHints.VALUE_ANTIALIAS_ON);
        g.setColor(new Color(100,116,139,45)); for(int x=0;x<getWidth();x+=45) g.drawLine(x,0,x,getHeight()); for(int y=0;y<getHeight();y+=45) g.drawLine(0,y,getWidth(),y);
        Set<String> hl=new HashSet<>(); for(List<String> p:paths) if(p!=null) for(int i=1;i<p.size();i++) hl.add(p.get(i-1)+">"+p.get(i));
        g.setFont(new Font("SansSerif",Font.PLAIN,11));
        for(Road r:C.roads){ Loc a=C.loc(r.a),b=C.loc(r.b); if(a==null||b==null) continue;
            boolean h=hl.contains(r.a+">"+r.b)||hl.contains(r.b+">"+r.a);
            boolean c=edge!=null&&((edge[0].equals(r.a)&&edge[1].equals(r.b))||(edge[0].equals(r.b)&&edge[1].equals(r.a)));
            g.setColor(c?DeliveryRouteOptimizer.AMB:h?DeliveryRouteOptimizer.LIME:DeliveryRouteOptimizer.GRAY);
            g.setStroke(new BasicStroke(h||c?5f:2.5f,BasicStroke.CAP_ROUND,BasicStroke.JOIN_ROUND,1f,r.ow?new float[]{8,6}:null,0f));
            g.drawLine((int)(a.x*sx()),(int)(a.y*sy()),(int)(b.x*sx()),(int)(b.y*sy()));
            if(h||labels){ g.setColor(DeliveryRouteOptimizer.LIME); g.drawString(Core.f(r.d)+" km",(int)((a.x+b.x)/2*sx())-14,(int)((a.y+b.y)/2*sy())-6); } }
        g.setStroke(new BasicStroke(2f));
        for(Loc l:C.locs){ int x=(int)(l.x*sx()),y=(int)(l.y*sy()); boolean cu=l.id.equals(cur),in=false; for(List<String> p:paths) if(p!=null&&p.contains(l.id)) in=true;
            g.setColor(cu?DeliveryRouteOptimizer.AMB:vis.contains(l.id)?new Color(0x34D399):in?DeliveryRouteOptimizer.LIME:DeliveryRouteOptimizer.BLUE);
            int rad=cu?9:7; g.fillOval(x-rad,y-rad,2*rad,2*rad); g.setColor(Color.WHITE); g.drawOval(x-rad,y-rad,2*rad,2*rad);
            g.setColor(DeliveryRouteOptimizer.TX); g.drawString(l.name,x-g.getFontMetrics().stringWidth(l.name)/2,y-12);
            if(dist!=null&&dist.containsKey(l.id)){ g.setColor(DeliveryRouteOptimizer.LIME); String s=Core.f(dist.get(l.id)); g.drawString(s,x-g.getFontMetrics().stringWidth(s)/2,y+24); } } }
    JPanel wrap(){ JPanel p=new JPanel(new BorderLayout()); p.add(this,BorderLayout.CENTER); info.setForeground(DeliveryRouteOptimizer.TX); p.add(info,BorderLayout.SOUTH); return p; }
}

/* ===== Main application ===== */
public class DeliveryRouteOptimizer extends JFrame {
    static final Color BG=new Color(0x101827),CARD=new Color(0x172136),LIME=new Color(0xA3E635),BLUE=new Color(0x38BDF8),GRAY=new Color(0x64748B),TX=new Color(0xE5E7EB),AMB=new Color(0xFBBF24);
    final Core C=new Core(); final List<JComboBox<Loc>> combos=new ArrayList<>(); Route last; int routesCalc=0; double routesKm=0; String baseline="";
    final MapPanel dashMap=new MapPanel(C), planMap=new MapPanel(C), bigMap=new MapPanel(C), vizMap=new MapPanel(C), multiMap=new MapPanel(C);
    JLabel stats=new JLabel(); JTextArea planOut=text(), mapOut=text(), vizMsg=text(), multiOut=text(), anaOut=text();
    DefaultTableModel locM=model("ID","Name","x","y"), roadM=model("From","To","km","min","One-way"), delM=model("Order","Customer","From","To","Agent","Status"), vizM=model("Node","Dist","Prev","State");
    JTable locT=new JTable(locM), roadT=new JTable(roadM), delT=new JTable(delM);
    JComboBox<Loc> pSrc=combo(), pDst=combo(), vSrc=combo(), vDst=combo(), mStart=combo();
    JRadioButton rDist=new JRadioButton("Shortest distance",true), rTime=new JRadioButton("Estimated time");
    JList<Loc> stopList=new JList<>(); JLabel heapLbl=new JLabel(" "); Res vr; int vi; javax.swing.Timer timer; JSlider speed=new JSlider(100,2000,900);
    JComboBox<String> vW=new JComboBox<>(new String[]{"distance","time"}), mW=new JComboBox<>(new String[]{"distance","time"}), dFilter=new JComboBox<>(new String[]{"All","Pending","In Transit","Delivered"}); JCheckBox retHub=new JCheckBox("Return to hub"); JTextField dSearch=new JTextField(12);

    static JTextArea text(){ JTextArea t=new JTextArea(); t.setEditable(false); t.setFont(new Font(Font.MONOSPACED,Font.PLAIN,12)); t.setLineWrap(true); t.setWrapStyleWord(true); return t; }
    static DefaultTableModel model(String... c){ return new DefaultTableModel(c,0){ public boolean isCellEditable(int r,int k){ return false; } }; }
    JComboBox<Loc> combo(){ JComboBox<Loc> c=new JComboBox<>(); combos.add(c); return c; }
    static JButton btn(String t,ActionListener a){ JButton b=new JButton(t); b.addActionListener(a); return b; }
    static JPanel row(Component... cs){ JPanel p=new JPanel(new FlowLayout(FlowLayout.LEFT,8,6)); for(Component c:cs) p.add(c); return p; }
    static void err(Component p,String m){ JOptionPane.showMessageDialog(p,m,"Invalid input",JOptionPane.WARNING_MESSAGE); }

    DeliveryRouteOptimizer(){
        super("Delivery Route Optimizer — Dijkstra + Min-Heap Priority Queue");
        JTabbedPane tabs=new JTabbedPane();
        tabs.add("Dashboard",dashboard()); tabs.add("Route Planner",planner()); tabs.add("Map View",mapView()); tabs.add("Locations & Roads",manage());
        tabs.add("DSA Visualizer",visualizer()); tabs.add("Multi-Stop",multi()); tabs.add("Deliveries",deliveries()); tabs.add("Analytics",new JScrollPane(anaOut)); tabs.add("Settings",settings());
        add(tabs); reload(); setDefaultCloseOperation(EXIT_ON_CLOSE); setSize(1100,720); setLocationRelativeTo(null); }

    JPanel dashboard(){ JPanel p=new JPanel(new BorderLayout(8,8)); p.setBorder(BorderFactory.createEmptyBorder(10,10,10,10));
        JLabel h=new JLabel("<html><h2 style='color:#A3E635'>Delivery Route Optimizer</h2>Road network as a weighted graph; Dijkstra + binary min-heap. Sample distances are <b>illustrative</b>, not real navigation data.</html>");
        stats.setForeground(BLUE); JPanel top=new JPanel(new GridLayout(2,1)); top.add(h); top.add(stats); p.add(top,BorderLayout.NORTH); p.add(dashMap.wrap(),BorderLayout.CENTER); return p; }

    JPanel planner(){ JPanel p=new JPanel(new BorderLayout(8,8)); ButtonGroup bg=new ButtonGroup(); bg.add(rDist); bg.add(rTime);
        JPanel f=row(new JLabel("Source:"),pSrc,new JLabel("Destination:"),pDst,rDist,rTime,btn("Calculate Route",e->calc()),btn("Clear",e->{last=null;planOut.setText("");planMap.paths.clear();planMap.repaint();}),btn("Reset",e->{last=null;planOut.setText("");planMap.paths.clear();planMap.repaint();pSrc.setSelectedIndex(0);pDst.setSelectedIndex(0);rDist.setSelected(true);}));
        p.add(f,BorderLayout.NORTH); JSplitPane sp=new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,planMap.wrap(),new JScrollPane(planOut)); sp.setResizeWeight(.55); p.add(sp,BorderLayout.CENTER); return p; }
    void calc(){ Loc s=(Loc)pSrc.getSelectedItem(),d=(Loc)pDst.getSelectedItem(); if(s==null||d==null){err(this,"Add locations first.");return;}
        last=C.compute(s.id,d.id,rTime.isSelected()); planOut.setText(C.describe(last)); planOut.setCaretPosition(0);
        planMap.paths.clear(); if(last.err==null){ planMap.paths.add(last.main.path); routesCalc++; routesKm+=last.main.km; }
        planMap.repaint(); reload(); }

    JPanel mapView(){ JPanel p=new JPanel(new BorderLayout(8,8)); bigMap.labels=true; JSplitPane sp=new JSplitPane(JSplitPane.HORIZONTAL_SPLIT,bigMap.wrap(),new JScrollPane(mapOut)); sp.setResizeWeight(.7);
        p.add(row(new JLabel("Shows the last route from the Route Planner (green). Solid = two-way, dashed = one-way.")),BorderLayout.NORTH); p.add(sp,BorderLayout.CENTER); return p; }

    JPanel manage(){ JPanel p=new JPanel(new BorderLayout(8,8)); JPanel c=new JPanel(new GridLayout(1,2,8,8));
        JPanel a=new JPanel(new BorderLayout()); a.add(new JScrollPane(locT)); a.add(row(btn("Add Location",e->addLoc()),btn("Edit Name",e->editLoc()),btn("Delete",e->delLoc())),BorderLayout.SOUTH);
        JPanel b=new JPanel(new BorderLayout()); b.add(new JScrollPane(roadT)); b.add(row(btn("Add Road",e->addRoad()),btn("Edit Weights",e->editRoad()),btn("Delete",e->delRoad())),BorderLayout.SOUTH);
        c.add(a); c.add(b); p.add(c); p.add(row(btn("Reset to Sample Data",e->{ if(JOptionPane.showConfirmDialog(this,"Reset all data to the sample graph?")==0){ C.reset(); last=null; clearMaps(); reload(); } }),new JLabel("Sample values are illustrative, not verified navigation data.")),BorderLayout.SOUTH); return p; }
    void clearMaps(){ for(MapPanel m:new MapPanel[]{dashMap,planMap,bigMap,vizMap,multiMap}){ m.paths.clear(); m.vis.clear(); m.cur=null; m.edge=null; m.dist=null; m.repaint(); } planOut.setText(""); }
    void addLoc(){ JTextField id=new JTextField(),n=new JTextField(),x=new JTextField(),y=new JTextField();
        if(JOptionPane.showConfirmDialog(this,new Object[]{"ID:",id,"Name:",n,"x (0-900):",x,"y (0-600):",y},"Add location",JOptionPane.OK_CANCEL_OPTION)!=0) return;
        String i=id.getText().trim(),nn=n.getText().trim(); int xi,yi; try{ xi=Integer.parseInt(x.getText().trim()); yi=Integer.parseInt(y.getText().trim()); }catch(Exception ex){ err(this,"x and y must be whole numbers."); return; }
        if(i.isEmpty()||nn.isEmpty()){ err(this,"ID and name are required."); return; } if(xi<0||xi>900||yi<0||yi>600){ err(this,"x must be 0–900 and y 0–600."); return; }
        for(Loc l:C.locs) if(l.id.equalsIgnoreCase(i)||l.name.equalsIgnoreCase(nn)){ err(this,"ID and name must be unique."); return; }
        C.locs.add(new Loc(i,nn,xi,yi)); reload(); }
    void editLoc(){ int r=locT.getSelectedRow(); if(r<0){ err(this,"Select a location row."); return; } Loc l=C.locs.get(r); String n=JOptionPane.showInputDialog(this,"New name",l.name);
        if(n==null||n.trim().isEmpty()) return; for(Loc o:C.locs) if(o!=l&&o.name.equalsIgnoreCase(n.trim())){ err(this,"Name already used."); return; } l.name=n.trim(); reload(); }
    void delLoc(){ int r=locT.getSelectedRow(); if(r<0){ err(this,"Select a location row."); return; } Loc l=C.locs.get(r);
        for(String[] d:C.deliv) if(d[2].equals(l.id)||d[3].equals(l.id)){ err(this,"Location is used by delivery "+d[0]+"."); return; }
        C.locs.remove(l); C.roads.removeIf(x->x.a.equals(l.id)||x.b.equals(l.id)); last=null; clearMaps(); reload(); }
    void addRoad(){ if(C.locs.size()<2){ err(this,"Need at least two locations."); return; } JComboBox<Loc> a=new JComboBox<>(C.locs.toArray(new Loc[0])),b=new JComboBox<>(C.locs.toArray(new Loc[0])); JTextField d=new JTextField(),t=new JTextField(); JCheckBox ow=new JCheckBox("One-way (from → to)");
        if(JOptionPane.showConfirmDialog(this,new Object[]{"From:",a,"To:",b,"Distance km:",d,"Time min:",t,ow},"Add road",JOptionPane.OK_CANCEL_OPTION)!=0) return;
        double dv,tv; try{ dv=Double.parseDouble(d.getText().trim()); tv=Double.parseDouble(t.getText().trim()); }catch(Exception ex){ err(this,"Distance and time must be numbers."); return; }
        String u=((Loc)a.getSelectedItem()).id,v=((Loc)b.getSelectedItem()).id; if(u.equals(v)){ err(this,"A road must connect two different locations."); return; }
        if(dv<0||tv<0||Double.isNaN(dv)||Double.isNaN(tv)||Double.isInfinite(dv)||Double.isInfinite(tv)){ err(this,"Weights must be finite and ≥ 0 (zero is allowed)."); return; }
        for(Road r:C.roads) if((r.a.equals(u)&&r.b.equals(v))||(r.a.equals(v)&&r.b.equals(u))){ err(this,"A road between these locations already exists."); return; }
        C.roads.add(new Road(u,v,dv,tv,ow.isSelected())); last=null; clearMaps(); reload(); }
    void editRoad(){ int r=roadT.getSelectedRow(); if(r<0){ err(this,"Select a road row."); return; } Road rd=C.roads.get(r);
        try{ String d=JOptionPane.showInputDialog(this,"Distance km",rd.d); if(d==null) return; String t=JOptionPane.showInputDialog(this,"Time min",rd.t); if(t==null) return;
            double dv=Double.parseDouble(d.trim()),tv=Double.parseDouble(t.trim()); if(dv<0||tv<0||Double.isNaN(dv)||Double.isNaN(tv)||Double.isInfinite(dv)||Double.isInfinite(tv)){ err(this,"Weights must be finite and ≥ 0."); return; } rd.d=dv; rd.t=tv; last=null; clearMaps(); reload(); }
        catch(NumberFormatException ex){ err(this,"Enter valid numbers."); } }
    void delRoad(){ int r=roadT.getSelectedRow(); if(r<0){ err(this,"Select a road row."); return; } C.roads.remove(r); last=null; clearMaps(); reload(); }

    JPanel visualizer(){ JPanel p=new JPanel(new BorderLayout(8,8)); vizMsg.setRows(4); vizMsg.setForeground(LIME);
        timer=new javax.swing.Timer(900,e->{ if(vr==null||vi>=vr.steps.size()-1){ timer.stop(); return; } vi++; showStep(); });
        speed.addChangeListener(e->timer.setDelay(2100-speed.getValue()));
        p.add(row(new JLabel("Source:"),vSrc,new JLabel("Dest:"),vDst,vW,btn("Load",e->loadViz()),btn("Play/Pause",e->{ if(vr==null) loadViz(); if(timer.isRunning()) timer.stop(); else timer.start(); }),btn("◀ Prev",e->{ if(vr!=null&&vi>0){ vi--; showStep(); } }),btn("Next ▶",e->{ if(vr==null) loadViz(); else if(vi<vr.steps.size()-1){ vi++; showStep(); } }),btn("Reset",e->loadViz()),new JLabel("Speed:"),speed),BorderLayout.NORTH);
        JPanel right=new JPanel(new BorderLayout()); heapLbl.setForeground(BLUE); right.add(heapLbl,BorderLayout.NORTH); right.add(new JScrollPane(new JTable(vizM))); right.setPreferredSize(new Dimension(340,300));
        p.add(vizMap.wrap(),BorderLayout.CENTER); p.add(right,BorderLayout.EAST);
        JPanel s=new JPanel(new BorderLayout()); s.add(new JScrollPane(vizMsg)); s.add(new JLabel(" Time complexity: O((V+E) log V) — adjacency list + binary min-heap (lazy deletion); needs non-negative weights. Replays snapshots from the real dijkstra()."),BorderLayout.SOUTH); p.add(s,BorderLayout.SOUTH); return p; }
    void loadViz(){ timer.stop(); Loc s=(Loc)vSrc.getSelectedItem(); if(s==null) return; vr=C.dijkstra(s.id,vW.getSelectedIndex()==1,true,null); vi=0; showStep(); }
    void showStep(){ Step st=vr.steps.get(vi); boolean end=vi==vr.steps.size()-1; Loc d=(Loc)vDst.getSelectedItem(); String txt="Step "+(vi+1)+"/"+vr.steps.size()+": "+st.msg;
        vizMap.vis=st.vis; vizMap.cur=st.cur; vizMap.edge=st.edge; vizMap.dist=st.dist; vizMap.paths.clear();
        if(end&&d!=null){ Loc s=(Loc)vSrc.getSelectedItem(); List<String> p=C.pathOf(vr,s.id,d.id); if(p!=null){ vizMap.paths.add(p); StringBuilder sb=new StringBuilder(); for(String x:p) sb.append(sb.length()>0?" → ":"").append(C.nm(x)); txt+="\nShortest path via predecessors: "+sb; } }
        vizMsg.setText(txt); heapLbl.setText(" Min-heap array: "+(st.heap.isEmpty()?"empty":st.heap));
        vizM.setRowCount(0); for(Loc l:C.locs) vizM.addRow(new Object[]{l.name,Core.f(st.dist.get(l.id)),st.prev.containsKey(l.id)?C.nm(st.prev.get(l.id)):"–",l.id.equals(st.cur)?"▶ current":st.vis.contains(l.id)?"✓ visited":"·"});
        vizMap.repaint(); }

    JPanel multi(){ JPanel p=new JPanel(new BorderLayout(8,8)); stopList.setVisibleRowCount(8); JPanel l=new JPanel(new BorderLayout()); l.add(new JLabel(" Select stops (Ctrl/Shift for several):"),BorderLayout.NORTH); l.add(new JScrollPane(stopList));
        l.add(row(new JLabel("Start:"),mStart,mW,retHub,btn("Plan stops",e->planMulti())),BorderLayout.SOUTH);
        multiOut.setText("Heuristic: nearest-neighbour ordering using Dijkstra shortest paths between stops. It is NOT guaranteed optimal — exact multi-stop optimisation (TSP / vehicle routing) is a separate NP-hard problem.");
        JPanel top=new JPanel(new GridLayout(1,2,8,8)); top.add(l); top.add(new JScrollPane(multiOut)); top.setPreferredSize(new Dimension(800,230)); p.add(top,BorderLayout.NORTH); p.add(multiMap.wrap(),BorderLayout.CENTER); return p; }
    void planMulti(){ Loc s=(Loc)mStart.getSelectedItem(); if(s==null) return; boolean time=mW.getSelectedIndex()==1; List<String> todo=new ArrayList<>(); for(Loc l:stopList.getSelectedValuesList()) if(!l.id.equals(s.id)) todo.add(l.id);
        if(todo.isEmpty()){ err(this,"Select at least one stop other than the start."); return; }
        String at=s.id; List<String> order=new ArrayList<>(), skipped=new ArrayList<>(); multiMap.paths.clear(); double km=0,min=0;
        while(!todo.isEmpty()){ Res r=C.dijkstra(at,time,false,null); String best=null; for(String t:todo) if(r.dist.get(t)<Core.INF&&(best==null||r.dist.get(t)<r.dist.get(best))) best=t;
            if(best==null){ skipped.addAll(todo); break; } List<String> p=C.pathOf(r,at,best); Info in=C.info(p,time); multiMap.paths.add(p); km+=in.km; min+=in.min; order.add(best); todo.remove(best); at=best; }
        if(retHub.isSelected()&&!at.equals(s.id)){ List<String> p=C.pathOf(C.dijkstra(at,time,false,null),at,s.id); if(p!=null){ Info in=C.info(p,time); multiMap.paths.add(p); km+=in.km; min+=in.min; } else skipped.add("(no way back to hub)"); }
        StringBuilder sb=new StringBuilder("Sequence (nearest-neighbour HEURISTIC):\n"+C.nm(s.id)); for(String o:order) sb.append(" → ").append(C.nm(o));
        sb.append(String.format("%n%nTotal: %.1f km | %.1f min | fuel %.2f L%n",km,min,km*C.fuel/100)); if(!skipped.isEmpty()) sb.append("Unreachable: ").append(skipped).append('\n'); sb.append("\nNot guaranteed optimal; exact multi-stop routing is a separate vehicle-routing problem.");
        multiOut.setText(sb.toString()); multiMap.repaint(); }

    JPanel deliveries(){ JPanel p=new JPanel(new BorderLayout(8,8)); ActionListener f=e->fillDeliveries(); dFilter.addActionListener(f); dSearch.addActionListener(f);
        p.add(row(new JLabel("Search:"),dSearch,dFilter,btn("Advance Status",e->{ int r=delT.getSelectedRow(); if(r<0){ err(this,"Select an order."); return; } String id=(String)delM.getValueAt(r,0);
            for(String[] d:C.deliv) if(d[0].equals(id)){ String[] o={"Pending","In Transit","Delivered"}; d[5]=o[(Arrays.asList(o).indexOf(d[5])+1)%3]; } reload(); }),btn("New Order",e->newOrder()),new JLabel("Statuses/tracking are SIMULATED — no live GPS.")),BorderLayout.NORTH);
        p.add(new JScrollPane(delT)); return p; }
    void fillDeliveries(){ delM.setRowCount(0); String q=dSearch.getText().toLowerCase(),fl=(String)dFilter.getSelectedItem();
        for(String[] d:C.deliv){ String all=(d[0]+d[1]+d[4]+C.nm(d[3])).toLowerCase(); if((fl.equals("All")||d[5].equals(fl))&&all.contains(q)) delM.addRow(new Object[]{d[0],d[1],C.nm(d[2]),C.nm(d[3]),d[4],d[5]}); } }
    void newOrder(){ JTextField c=new JTextField(),a=new JTextField(); JComboBox<Loc> f=new JComboBox<>(C.locs.toArray(new Loc[0])),t=new JComboBox<>(C.locs.toArray(new Loc[0]));
        if(JOptionPane.showConfirmDialog(this,new Object[]{"Customer:",c,"From:",f,"To:",t,"Agent:",a},"New order",JOptionPane.OK_CANCEL_OPTION)!=0) return;
        if(c.getText().trim().isEmpty()||a.getText().trim().isEmpty()||f.getSelectedItem()==null||f.getSelectedItem()==t.getSelectedItem()){ err(this,"Fill all fields; source and destination must differ."); return; }
        C.deliv.add(new String[]{"ORD-"+(101+C.deliv.size()),c.getText().trim(),((Loc)f.getSelectedItem()).id,((Loc)t.getSelectedItem()).id,a.getText().trim(),"Pending"}); reload(); }

    JPanel settings(){ JPanel p=new JPanel(new BorderLayout()); JTextField fu=new JTextField(String.valueOf(C.fuel),6),bl=new JTextField(6);
        JTextArea info=text(); info.setText("Project: Delivery Route Optimizer Using Dijkstra's Algorithm and Priority Queue\nCourse: Data Structures and Algorithms-3 (25CS2103E)\nTeam 10: Bathula Neha (2520090013), Siri Chandana (2520090198)\nGuide: Mrs. Ch. Anitha, Assistant Professor, CS&IT\n\nGraph: adjacency list. Priority queue: binary min-heap. Dijkstra needs non-negative weights; path rebuilt from predecessors.\nSample data is illustrative. Fuel and time are estimates under stated assumptions — no live traffic.");
        p.add(row(new JLabel("Fuel (L/100km):"),fu,btn("Save",e->{ try{ double v=Double.parseDouble(fu.getText().trim()); if(!(v>0)) throw new Exception(); C.fuel=v; reload(); }catch(Exception ex){ err(this,"Enter a positive number."); } }),btn("Export last route as CSV",e->exportCsv()),new JLabel("Baseline km (Analytics):"),bl,btn("Set",e->{ try{ double v=Double.parseDouble(bl.getText().trim()); if(!(v>0)) throw new Exception(); baseline=bl.getText().trim(); reload(); }catch(Exception ex){ err(this,"Enter a positive number."); } }),new JLabel(" (calculate a route first)")),BorderLayout.NORTH); p.add(new JScrollPane(info)); return p; }
    void exportCsv(){ if(last==null||last.err!=null){ err(this,"Calculate a route first."); return; } JFileChooser fc=new JFileChooser(); fc.setSelectedFile(new File("route_report.csv")); if(fc.showSaveDialog(this)!=0) return;
        try(PrintWriter w=new PrintWriter(fc.getSelectedFile(),"UTF-8")){ w.println("From,To,Distance_km,Time_min"); for(Object[] s:last.main.segs) w.printf("\"%s\",\"%s\",%.1f,%.1f%n",C.nm((String)s[0]),C.nm((String)s[1]),(Double)s[2],(Double)s[3]);
            w.printf("TOTAL,,%.1f,%.1f%nFuel_L (assumed %.1f L/100km),,%.2f,%nNote,Illustrative sample data%n",last.main.km,last.main.min,C.fuel,last.main.km*C.fuel/100); JOptionPane.showMessageDialog(this,"Saved."); }
        catch(IOException ex){ err(this,"Could not save: "+ex.getMessage()); } }

    void analytics(){ StringBuilder sb=new StringBuilder("ANALYTICS  (values computed from illustrative sample distances; fuel = km × "+C.fuel+" L/100km is an assumption; no live traffic data)\n\n"); double tk=0; int done=0,n=0;
        StringBuilder bars=new StringBuilder("Distance per delivery (optimised):\n"); for(String[] d:C.deliv){ Route r=C.compute(d[2],d[3],false); double km=r.err==null?r.main.km:0; tk+=km; n++; if(d[5].equals("Delivered")) done++; bars.append(String.format("%-8s %5.1f km %s%n",d[0],km,"█".repeat((int)Math.round(km*2)))); }
        sb.append(String.format("Total distance: %.1f km%nAverage route: %.1f km%nEst. fuel: %.2f L (simulated)%nCompleted deliveries: %d / %d%n%n",tk,n==0?0:tk/n,tk*C.fuel/100,done,n)).append(bars);
        sb.append("\nBaseline vs optimised: set a baseline km in Settings after calculating a route.\n"); if(!baseline.isEmpty()&&last!=null&&last.err==null){ double b=Double.parseDouble(baseline); sb.append(String.format("Baseline %.1f km vs optimised %.1f km → %.1f%% %s (baseline is user-provided)%n",b,last.main.km,Math.abs(b-last.main.km)/b*100,b>=last.main.km?"shorter":"longer")); }
        anaOut.setText(sb.toString()); }

    void reload(){
        for(JComboBox<Loc> c:combos){ Loc sel=(Loc)c.getSelectedItem(); c.removeAllItems(); for(Loc l:C.locs) c.addItem(l); if(sel!=null&&C.loc(sel.id)!=null) c.setSelectedItem(C.loc(sel.id)); }
        locM.setRowCount(0); for(Loc l:C.locs) locM.addRow(new Object[]{l.id,l.name,l.x,l.y});
        roadM.setRowCount(0); for(Road r:C.roads) roadM.addRow(new Object[]{C.nm(r.a),C.nm(r.b),r.d,r.t,r.ow?"yes":"no"});
        stopList.setListData(C.locs.toArray(new Loc[0])); fillDeliveries();
        stats.setText(String.format(" 📍 %d locations   🛣 %d roads   🧭 %d routes calculated   📏 %.1f km planned   🚚 %d deliveries",C.locs.size(),C.roads.size(),routesCalc,routesKm,C.deliv.size()));
        Route show=last; if(show==null&&C.loc("hub")!=null&&C.loc("gac")!=null) show=C.compute("hub","gac",false);
        for(MapPanel m:new MapPanel[]{dashMap,bigMap}){ m.paths.clear(); if(show!=null&&show.err==null) m.paths.add(show.main.path); m.repaint(); }
        mapOut.setText(show==null?"No route yet.":C.describe(show)); analytics(); repaint(); }

    public static void main(String[] a) throws Exception {
        if(a.length>0&&a[0].equals("--test")){ Core.selfTest(); return; }
        Object[][] ui={{"Panel.background",BG},{"Label.foreground",TX},{"TabbedPane.background",BG},{"TabbedPane.foreground",TX},{"TabbedPane.contentAreaColor",BG},{"TabbedPane.selected",CARD},{"TextArea.background",CARD},{"TextArea.foreground",TX},{"Table.background",CARD},{"Table.foreground",TX},{"TableHeader.background",BG},{"TableHeader.foreground",LIME},{"ComboBox.background",CARD},{"ComboBox.foreground",TX},{"TextField.background",CARD},{"TextField.foreground",TX},{"TextField.caretForeground",TX},{"Button.background",CARD},{"Button.foreground",TX},{"List.background",CARD},{"List.foreground",TX},{"CheckBox.background",BG},{"CheckBox.foreground",TX},{"RadioButton.background",BG},{"RadioButton.foreground",TX},{"OptionPane.background",BG},{"OptionPane.messageForeground",TX},{"ScrollPane.background",BG},{"Slider.background",BG},{"SplitPane.background",BG}};
        UIManager.setLookAndFeel(UIManager.getCrossPlatformLookAndFeelClassName()); for(Object[] o:ui) UIManager.put(o[0],o[1]);
        SwingUtilities.invokeLater(()->new DeliveryRouteOptimizer().setVisible(true)); }
}
