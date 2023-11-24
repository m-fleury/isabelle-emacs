/***************************************************************************
  Title:      graphbrowser/GraphBrowser.java
  Author:     Stefan Berghofer, TU Muenchen
  Options:    :tabSize=4:

  This is the graph browser's main class. It contains the "main(...)"
  method, which is used for the stand-alone version.
  Note: GraphBrowser is designed for the 1.1.x version of the JDK.
***************************************************************************/

package isabelle.graphbrowser;

import java.awt.*;
import java.io.*;
import java.util.*;
import java.net.*;
import isabelle.awt.*;

public class GraphBrowser extends Panel {
	GraphView gv;
	TreeBrowser tb=null;
	String gfname;

	static Frame f;

	public GraphBrowser(String name) {
		gfname=name;
	}

	public GraphBrowser() {}

	public void showWaitMessage() {
		f.setCursor(new Cursor(Cursor.WAIT_CURSOR));
	}

	public void showReadyMessage() {
		f.setCursor(new Cursor(Cursor.DEFAULT_CURSOR));
	}

	public void viewFile(String fname) {
		try {
            String path = gfname.substring(0, gfname.lastIndexOf('/') + 1);
            Reader rd;
            BufferedReader br;
            String line, text = "";

            try {
                rd = new BufferedReader(new InputStreamReader((new URI(fname)).toURL().openConnection().getInputStream()));
            } catch (Exception exn) {
                rd = new FileReader(path + fname);
            }
            br = new BufferedReader(rd);

            while ((line = br.readLine()) != null)
                text += line + "\n";

            if (fname.endsWith(".html")) {
                /**** convert HTML to text (just a quick hack) ****/

                String buf="";
                char[] text2,text3;
                int i,j=0;
                boolean special=false, html=false;
                char ctrl;

                text2 = text.toCharArray();
                text3 = new char[text.length()];
                for (i = 0; i < text.length(); i++) {
                    char c = text2[i];
                    if (c == '&') {
                        special = true;
                        buf = "";
                    } else if (special) {
                        if (c == ';') {
                            special = false;
                            if (buf.equals("lt"))
                                text3[j++] = '<';
                            else if (buf.equals("gt"))
                                text3[j++] = '>';
                            else if (buf.equals("amp"))
                                text3[j++] = '&';
                        } else
                            buf += c;
                    } else if (c == '<') {
                        html = true;
                        ctrl = text2[i+1];
                    } else if (c == '>')
                        html = false;
                    else if (!html)
                        text3[j++] = c;
                }
                text = String.valueOf(text3);
            }

            Frame f=new TextFrame(fname.substring(fname.lastIndexOf('/')+1),text);
            f.setSize(500,600);
            f.setVisible(true);
		} catch (Exception exn) {
			System.err.println("Can't read file "+fname);
		}
	}
				
	public void PS(String fname,boolean printable) throws IOException {
		gv.PS(fname,printable);
	}

	public boolean isEmpty() {
		return tb==null;
	}

	public void initBrowser(InputStream is, boolean noAWT) {
		try {
			Font font = noAWT ? null : new Font("Helvetica", Font.PLAIN, 12);
			TreeNode tn = new TreeNode("Root", "", -1, true);
			gv = new GraphView(new Graph(is, tn), this, font);
			tb = new TreeBrowser(tn, gv, font);
			gv.setTreeBrowser(tb);
			Vector v = new Vector(10,10);
			tn.collapsedDirectories(v);
			gv.collapseDir(v);

			ScrollPane scrollp1 = new ScrollPane();
			ScrollPane scrollp2 = new ScrollPane();
			scrollp1.add(gv);
			scrollp2.add(tb);
			scrollp1.getHAdjustable().setUnitIncrement(20);
			scrollp1.getVAdjustable().setUnitIncrement(20);
			scrollp2.getHAdjustable().setUnitIncrement(20);
			scrollp2.getVAdjustable().setUnitIncrement(20);
			Component gv2 = new Border(scrollp1, 3);
			Component tb2 = new Border(scrollp2, 3);
			GridBagLayout gridbag = new GridBagLayout();
			GridBagConstraints cnstr = new GridBagConstraints();
			setLayout(gridbag);
			cnstr.fill = GridBagConstraints.BOTH;
			cnstr.insets = new Insets(5,5,5,5);
			cnstr.weightx = 1;
			cnstr.weighty = 1;
			cnstr.gridwidth = 1;
			gridbag.setConstraints(tb2,cnstr);
			add(tb2);
			cnstr.weightx = 2.5;
			cnstr.gridwidth = GridBagConstraints.REMAINDER;
			gridbag.setConstraints(gv2,cnstr);
			add(gv2);
		} catch (IOException exn) {
			System.err.println("\nI/O error while reading graph file.");
		} catch (ParseError exn) {
			System.err.println("\nParse error in graph file:");
			System.err.println(exn.getMessage());
			System.err.println("\nSyntax:\n<vertexname> <vertexID> <dirname> [ + ] <path> [ < | > ] [ <vertexID> [ ... [ <vertexID> ] ... ] ] ;");
		}
	}		

	public static void main(String[] args) {
		try {
			GraphBrowser gb=new GraphBrowser(args.length > 0 ? args[0] : "");
			if (args.length > 0) {
				InputStream is=new FileInputStream(args[0]);
				gb.initBrowser(is, args.length > 1);
				is.close();
			}
			if (args.length > 1) {
                            try {
			      if (args[1].endsWith(".ps"))
                                gb.gv.PS(args[1], true);
                              else if (args[1].endsWith(".eps"))
                                gb.gv.PS(args[1], false);
                              else
                                System.err.println("Unknown file type: " + args[1]);
                            } catch (IOException exn) {
                              System.err.println("Unable to write file " + args[1]);
                            }
                        } else {
			    f=new GraphBrowserFrame(gb);
			    f.setSize(700,500);
			    f.setVisible(true);
                        }
		} catch (IOException exn) {
			System.err.println("Can't open graph file "+args[0]);
		}
	}
}
