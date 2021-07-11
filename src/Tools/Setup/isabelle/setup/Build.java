/*  Title:      Tools/Setup/isabelle/setup/Build.java
    Author:     Makarius

Build Isabelle/Scala/Java modules.
*/

package isabelle.setup;


import java.io.BufferedOutputStream;
import java.io.File;
import java.io.IOException;
import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardCopyOption;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.List;
import java.util.Locale;
import java.util.Properties;
import java.util.TreeMap;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarFile;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import java.util.stream.Stream;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;

import scala.tools.nsc.MainClass;


public class Build
{
    /** context **/

    public static String BUILD_PROPS = "build.props";
    public static String COMPONENT_BUILD_PROPS = "etc/build.props";

    public static Context directory_context(Path dir)
        throws IOException
    {
        Properties props = new Properties();
        props.load(Files.newBufferedReader(dir.resolve(BUILD_PROPS)));
        return new Context(dir, props);
    }

    public static Context component_context(Path dir)
        throws IOException
    {
        Properties props = new Properties();
        Path build_props = dir.resolve(COMPONENT_BUILD_PROPS);
        if (Files.exists(build_props)) { props.load(Files.newBufferedReader(build_props)); }
        return new Context(dir, props);
    }

    public static List<Context> component_contexts()
        throws IOException, InterruptedException
    {
        List<Context> result = new LinkedList<Context>();
        for (String p : Environment.getenv("ISABELLE_COMPONENTS").split(":", -1)) {
            if (!p.isEmpty()) {
                Path dir = Path.of(Environment.platform_path(p));
                if (Files.exists(dir.resolve(COMPONENT_BUILD_PROPS))) {
                    result.add(component_context(dir));
                }
            }
        }
        return List.copyOf(result);
    }

    private static String sha_digest(MessageDigest sha, String name)
    {
        String digest = String.format(Locale.ROOT, "%040x", new BigInteger(1, sha.digest()));
        return digest + " " + name + "\n";
    }

    public static class Context
    {
        private final Path _dir;
        private final Properties _props;

        public Context(Path dir, Properties props)
        {
            _dir = dir;
            _props = props;
        }

        @Override public String toString() { return _dir.toString(); }

        public String name() { return _props.getProperty("name", _dir.toFile().getName()); }
        public String description() { return _props.getProperty("description", name()); }

        public String lib_name() { return _props.getProperty("lib", "lib") + "/" + name(); }
        public String jar_name() { return lib_name() + ".jar"; }

        public String scalac_options() { return _props.getProperty("scalac_options", ""); }
        public String javac_options() { return _props.getProperty("javac_options", ""); }

        public String main() { return _props.getProperty("main", ""); }

        private List<String> get_list(String name)
        {
            List<String> list = new LinkedList<String>();
            for (String s : _props.getProperty(name, "").split("\\s+")) {
                if (!s.isEmpty()) { list.add(s); }
            }
            return List.copyOf(list);
        }
        public List<String> requirements() { return get_list("requirements"); }
        public List<String> sources() { return get_list("sources"); }
        public List<String> resources() { return get_list("resources"); }
        public List<String> services() { return get_list("services"); }

        public boolean is_vacuous()
        {
            return sources().isEmpty() && resources().isEmpty() && services().isEmpty();
        }

        public Path path(String file)
            throws IOException, InterruptedException
        {
            return _dir.resolve(Environment.expand_platform_path(file));
        }
        public boolean exists(String file)
            throws IOException, InterruptedException
        {
            return Files.exists(path(file));
        }

        // historic
        public Path shasum_path()
            throws IOException, InterruptedException
        {
            return path(lib_name() + ".shasum");
        }

        public String item_name(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(0, i) : s;
        }

        public String item_target(String s)
        {
            int i = s.indexOf(':');
            return i > 0 ? s.substring(i + 1) : s;
        }

        public String shasum(String name, List<Path> paths)
            throws IOException, NoSuchAlgorithmException
        {
            MessageDigest sha = MessageDigest.getInstance("SHA");
            for (Path file : paths) {
                if (Files.exists(file)) {
                    sha.update(Files.readAllBytes(file));
                }
                else {
                    throw new RuntimeException(
                        "Missing input file " + Environment.quote(file.toString()));
                }
            }
            return sha_digest(sha, name);
        }

        public String shasum(String file)
            throws IOException, NoSuchAlgorithmException, InterruptedException
        {
            return shasum(file, List.of(path(file)));
        }

        public String shasum_props()
            throws NoSuchAlgorithmException
        {
            TreeMap<String,Object> sorted = new TreeMap<String,Object>();
            for (Object x : _props.entrySet()) {
                sorted.put(x.toString(), _props.get(x));
            }
            MessageDigest sha = MessageDigest.getInstance("SHA");
            sha.update(sorted.toString().getBytes(StandardCharsets.UTF_8));
            return sha_digest(sha, "<props>");
        }
    }


    /** compile sources **/

    private static void add_options(List<String> options_list, String options)
    {
        if (options != null) {
            for (String s : options.split("\\s+")) {
                if (!s.isEmpty()) { options_list.add(s); }
            }
        }
    }

    public static void compile_scala_sources(
        Path target_dir, String more_options, List<Path> deps, List<Path> sources)
        throws IOException, InterruptedException
    {
        ArrayList<String> args = new ArrayList<String>();
        add_options(args, Environment.getenv("ISABELLE_SCALAC_OPTIONS"));
        add_options(args, more_options);
        args.add("-d");
        args.add(target_dir.toString());
        args.add("-bootclasspath");
        args.add(Environment.join_platform_paths(deps));
        args.add("--");

        boolean scala_sources = false;
        for (Path p : sources) {
            args.add(p.toString());
            if (p.toString().endsWith(".scala")) { scala_sources = true; }
        }
        if (scala_sources) {
            MainClass main = new MainClass();
            boolean ok = main.process(args.toArray(String[]::new));
            if (!ok) throw new RuntimeException("Failed to compile Scala sources");
        }
    }

    public static void compile_java_sources(
        Path target_dir, String more_options, List<Path> deps, List<Path> sources)
        throws IOException, InterruptedException
    {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        StandardJavaFileManager file_manager =
            compiler.getStandardFileManager(null, Locale.ROOT, StandardCharsets.UTF_8);

        List<String> options = new LinkedList<String>();
        add_options(options, Environment.getenv("ISABELLE_JAVAC_OPTIONS"));
        add_options(options, more_options);
        options.add("-d");
        options.add(target_dir.toString());
        options.add("-classpath");
        options.add(Environment.join_platform_paths(deps));

        List<JavaFileObject> java_sources = new LinkedList<JavaFileObject>();
        for (Path p : sources) {
            if (p.toString().endsWith(".java")) {
                for (JavaFileObject o : file_manager.getJavaFileObjectsFromPaths(List.of(p))) {
                    java_sources.add(o);
                }
            }
        }
        if (!java_sources.isEmpty()) {
            boolean ok = compiler.getTask(null, file_manager, null, options, null, java_sources).call();
            if (!ok) throw new RuntimeException("Failed to compile Java sources");
        }
    }


    /** shasum for jar content **/

    private static String SHASUM = "META-INF/isabelle/shasum";

    public static String get_shasum(Path jar_path)
        throws IOException
    {
        if (Files.exists(jar_path)) {
            try (JarFile jar_file = new JarFile(jar_path.toFile()))
            {
                JarEntry entry = jar_file.getJarEntry(SHASUM);
                if (entry != null) {
                    byte[] bytes = jar_file.getInputStream(entry).readAllBytes();
                    return new String(bytes, StandardCharsets.UTF_8);
                }
                else { return ""; }
            }
        }
        else { return ""; }
    }

    public static void create_shasum(Path dir, String shasum)
        throws IOException
    {
        Path path = dir.resolve(SHASUM);
        Files.createDirectories(path.getParent());
        Files.writeString(path, shasum);
    }


    /** services **/

    private static String SERVICES = "META-INF/isabelle/services";

    public static List<String> get_services(Path jar_path)
        throws IOException
    {
        if (Files.exists(jar_path)) {
            try (JarFile jar_file = new JarFile(jar_path.toFile()))
            {
                JarEntry entry = jar_file.getJarEntry(SERVICES);
                if (entry != null) {
                    byte[] bytes = jar_file.getInputStream(entry).readAllBytes();
                    return Library.split_lines(new String(bytes, StandardCharsets.UTF_8));
                }
                else { return List.of(); }
            }
        }
        else { return List.of(); }
    }

    public static void create_services(Path dir, List<String> services)
        throws IOException
    {
        if (!services.isEmpty()) {
            Path path = dir.resolve(SERVICES);
            Files.createDirectories(path.getParent());
            Files.writeString(path, Library.cat_lines(services));
        }
    }


    /** create jar **/

    public static void create_jar(Path dir, String main, Path jar)
        throws IOException
    {
        Files.createDirectories(dir.resolve(jar).getParent());
        Files.deleteIfExists(jar);

        Manifest manifest = new Manifest();
        Attributes attributes = manifest.getMainAttributes();
        attributes.put(Attributes.Name.MANIFEST_VERSION, "1.0");
        attributes.put(new Attributes.Name("Created-By"),
            System.getProperty("java.version") + " (" + System.getProperty("java.vendor") + ")");
        if (!main.isEmpty()) { attributes.put(Attributes.Name.MAIN_CLASS, main); }

        try (JarOutputStream out =
            new JarOutputStream(new BufferedOutputStream(Files.newOutputStream(jar)), manifest))
        {
            for (Path path : Files.walk(dir).sorted().toArray(Path[]::new)) {
                boolean is_dir = Files.isDirectory(path);
                boolean is_file = Files.isRegularFile(path);
                if (is_dir || is_file) {
                    String name = Environment.slashes(dir.relativize(path).toString());
                    if (!name.isEmpty()) {
                        JarEntry entry = new JarEntry(is_dir ? name + "/" : name);
                        entry.setTime(path.toFile().lastModified());
                        out.putNextEntry(entry);
                        if (is_file) { out.write(Files.readAllBytes(path)); }
                        out.closeEntry();
                    }
                }
            }
        }
    }


    /** classpath **/

    public static List<Path> classpath()
        throws IOException, InterruptedException
    {
        List<Path> result = new LinkedList<Path>();
        for (Context context : component_contexts()) {
            result.add(context.path(context.jar_name()));
        }
        return List.copyOf(result);
    }

    public static List<String> services()
        throws IOException, InterruptedException
    {
        List<String> result = new LinkedList<String>();
        for (Context context : component_contexts()) {
            for (String s : context.services()) {
                result.add(s);
            }
        }
        return List.copyOf(result);
    }


    /** build **/

    public static void build(Context context, boolean fresh)
        throws IOException, InterruptedException, NoSuchAlgorithmException
    {
        String jar_name = context.jar_name();
        Path jar_path = context.path(jar_name);

        List<String> requirements = context.requirements();
        List<String> resources = context.resources();
        List<String> sources = context.sources();

        Files.deleteIfExists(context.shasum_path());

        if (context.is_vacuous()) { Files.deleteIfExists(jar_path); }
        else {
            String shasum_old = get_shasum(jar_path);
            String shasum;
            List<Path> compiler_deps = new LinkedList<Path>();
            {
                StringBuilder _shasum = new StringBuilder();
                _shasum.append(context.shasum_props());
                for (String s : requirements) {
                    if (s.startsWith("env:")) {
                        List<Path> paths = new LinkedList<Path>();
                        for (String p : Environment.getenv(s.substring(4)).split(":", -1)) {
                            if (!p.isEmpty()) {
                                Path path = Path.of(Environment.platform_path(p));
                                compiler_deps.add(path);
                                paths.add(path);
                            }
                        }
                        _shasum.append(context.shasum(s, paths));
                    }
                    else {
                        compiler_deps.add(context.path(s));
                        _shasum.append(context.shasum(s));
                    }
                }
                for (String s : resources) {
                    _shasum.append(context.shasum(context.item_name(s)));
                }
                for (String s : sources) { _shasum.append(context.shasum(s)); }
                shasum = _shasum.toString();
            }
            if (fresh || !shasum_old.equals(shasum)) {
                System.out.println(
                    "### Building " + context.description() + " (" + jar_path + ") ...");

                String isabelle_class_path = Environment.getenv("ISABELLE_CLASSPATH");

                Path build_dir = Files.createTempDirectory("isabelle");
                try {
                    /* compile sources */

                    for (String s : isabelle_class_path.split(":", -1)) {
                        if (!s.isEmpty()) {
                          compiler_deps.add(Path.of(Environment.platform_path(s)));
                        }
                    }

                    List<Path> compiler_sources = new LinkedList<Path>();
                    for (String s : sources) { compiler_sources.add(context.path(s)); }

                    compile_scala_sources(
                        build_dir, context.scalac_options(), compiler_deps, compiler_sources);

                    compiler_deps.add(build_dir);
                    compile_java_sources(
                        build_dir, context.javac_options(), compiler_deps, compiler_sources);


                    /* copy resources */

                    for (String s : context.resources()) {
                        String name = context.item_name(s);
                        String target = context.item_target(s);
                        Path file_name = Path.of(name).normalize().getFileName();
                        Path target_path = Path.of(target).normalize();

                        Path target_dir;
                        Path target_file;
                        {
                            if (target.endsWith("/") || target.endsWith("/.")) {
                                target_dir = build_dir.resolve(target_path);
                                target_file = target_dir.resolve(file_name);
                            }
                            else {
                                target_file = build_dir.resolve(target_path);
                                target_dir = target_file.getParent();
                            }
                        }
                        Files.createDirectories(target_dir);
                        Files.copy(context.path(name), target_file,
                            StandardCopyOption.COPY_ATTRIBUTES);
                    }


                    /* packaging */

                    create_shasum(build_dir, shasum);
                    create_services(build_dir, context.services());
                    create_jar(build_dir, context.main(), jar_path);
                }
                finally {
                    try (Stream<Path> walk = Files.walk(build_dir)) {
                        walk.sorted(Comparator.reverseOrder())
                            .map(Path::toFile)
                            .forEach(File::delete);
                    }
                }
            }
        }
    }

    public static void build_components(boolean fresh)
        throws IOException, InterruptedException, NoSuchAlgorithmException
    {
        for (Context context : component_contexts()) {
            build(context, fresh);
        }
    }
}
