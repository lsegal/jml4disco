#!/usr/bin/ruby

$boogie_path = "org.eclipse.jdt.core/compiler/org/jmlspecs/jml4/boogie/"
$tests_path  = "org.jmlspecs.eclipse.jdt.core.tests/src/org/jmlspecs/eclipse/jdt/core/tests/boogie/"

class Group
    GROUPS = { 
        "stmt" => "Statements", 
        "expr" => "Expressions", 
        "array" => "Arrays", 
        "decl" => "Declarations",
        "field" => "Fields",
        "lit" => "Literals", 
        "jml" => "JML", 
        "javadoc" => "Javadoc", 
        "misc" => "Miscellaneous"
    }

    def initialize(value)
        if !GROUPS.keys.include?(value) || !self.class.order.include?(value)
            STDERR.puts "invalid group=#{value}"
        end
        
        @val = value
    end

    def key
        @val
    end

    def name
        GROUPS[@val]
    end

    def self.order
        ["stmt", "expr", "field", "decl", "lit", "jml", "array", "javadoc", "misc"]
    end
end

class Priority
    def initialize(priority)
        @pri = priority
    end
        
    def value; @pri end

    def colour
        case @pri
        when "3"
            return "#f00"
        when "?"
            return "#006"
        end
    end

    def html
        case @pri
        when nil
            return ""
        when "0"
            return "IGNORED"
        when "1"
            return "LOW"
        when "2"
            return "MED"
        when "3"
            return "<strong>HIGH</strong>"
        when "?"
            return "<em>REVISE</em>"
        end
    end
end

class TestTraceability
    attr_accessor :file, :line, :pass, :name, :adapter

    def initialize(file, line, name, pass = false, adapter = nil) 
        self.file = file
        self.line = line
        self.name = name
        self.pass = pass 
        self.adapter = adapter
    end

    def html
        <<-eof
            <a href="/trac/browser/JML4/dev/trunk/#{$tests_path}#{file}#L#{line}"
                style="color:#{color}" title="#{file}: #{name}#{adapter}">#{value}</a>
        eof
    end

    def color
        pass ? '#006' : '#f00;font-weight:bold;'
    end

    def value
        pass ? 'P' : 'F'
    end

    def adapter
        @adapter ? " (Adapter)" : ""
    end
end

class NodeType
    attr_reader :method, :scope, :priority, :group, :done, :tests

    def initialize(method, scope, priority, group = "misc", done = false)
        self.method = method
        self.scope = scope
        self.priority = Priority.new(priority)
        self.group = Group.new(group)
        self.done = done
    end

    def tests
        $traceability.has_key?(method) ? $traceability[method] : []
    end

private
    attr_writer :method, :scope, :priority, :group, :done
end

class TableEmitter
    def self.emit(o)
        <<-eof
            <table style='border-collapse:collapse' border=1 cellpadding=3>
                <tr>
                    <th style='font-weight:bold' align='left'></th>
                    <th style='font-weight:bold' align='left'>Node Type</th>
                    <th style='font-weight:bold' align='left'>Scope</th>
                    <th style='font-weight:bold' align='left'>Completed</th>
                    <th style='font-weight:bold' align='left'>Priority</th>
                    <th style='font-weight:bold' align='left'>Test Traceability</th>
                </tr>

                #{emit_groups(o)}
            </table>
        eof
    end

    def self.emit_groups(o)
        i = 1
        Group.order.map do |group|
            str, tot = TableGroupEmitter.emit(o, group, i)
            i += tot
            str
        end.join("\n")
    end
end

class TableGroupEmitter
    def self.emit(o, grp, start)
        items = o.find_all {|x| x.group.key == grp }
        s = <<-eof
            <tr>
                <th style='font-weight:bold' align='left' colspan='6'>
                    #{::Group::GROUPS[grp]}
                </th>
            </tr>
            #{emit_items(items, grp, start)}
        eof
        [s, items.size]
    end

    def self.emit_items(items, grp, start)
        str = []
        items.each_with_index do |e, i| 
            str << TableRowEmitter.emit(e, start + i) 
        end
        str.join("\n")
    end
end

class TableRowEmitter
    def self.emit(o, i)
        if o.priority.value == "0"
            <<-eof
                <tr style='color:#999;font-style:italic'>
                     <td align='left'>#{i}</td>
                     <td align='left'><em>#{o.method}</em></td>
                     <td align='left'><em>#{o.scope}</em></td>
                     <td></td>
                     <td align='left'><em>IGNORED</em></td>
                     <td></td>
                 </tr>
            eof
        else
            style = ''
            tests_pass = o.tests.all? {|t| t.pass }
            tests_pass_color = tests_pass ? '#bea' : '#ffa'
            if o.done
                style = 'background-color:' + tests_pass_color
            elsif o.priority.colour
                style = 'color:'+o.priority.colour
            end

            if !tests_pass
                style += ';background-color:' + tests_pass_color
            end

            <<-eof
                <tr style='#{style}'>
                    <td align='left'>#{i}</td>
                    <th align='left'>#{o.method}</th>
                    <td align='left'>#{o.scope}</td>
                    <td align='center'><strong>#{o.done ? 'X':''}</strong></td>
                    <td align='left'>#{o.priority.html}</td>
                    <td align='left'>#{o.tests.map {|t| t.html }.join(", ")}</td>
                </tr>
            eof
        end
    end
end

def parse_tests(file, adapter_test = false)
    lines = File.read("../" + $tests_path + file).split(/\r?\n/)
    out = {}
    lines.each_with_index do |line, index|
	    if line =~ /public void (test\S+)/
            name = $1
		    if lines[index - 1] =~ /^\s*\/\//
                prevline = lines[index - 1]
                pass = !(prevline =~ /\bTODO\b/)
                terms = prevline[/term=(\S+)/, 1] 
                adapter = prevline[/\badapter=(\S+)/, 1]
                adapter = adapter == "pass" if adapter
                next unless terms
                terms.split(',').each do |term|
                    out[term] ||= []
                    out[term] << TestTraceability.new(file, index+1, name, pass)
                    out[term] << TestTraceability.new(file, index+1, name, adapter, true) if adapter
                end
            end
        end
    end
    out
end

def parse_boogie(str)
    lines = str.split(/\r?\n/)
    out = []
    lines.each_with_index do |line, index|
	    if line =~ /public boolean visit\((\S+) term, (\S+) .+?\)/  
		    method, scope, done, priority, group = $1, $2, true, nil, nil
            method = method.split('.').last
            scope = scope == "BlockScope" ? "method" : "class"
		    if lines[index - 1] =~ /^\s*\/\//
                prevline = lines[index - 1]
                done = !(prevline =~ /\bTODO\b/)
                priority = prevline[/\spriority=(\S+)/, 1]
                group = prevline[/\sgroup=(\S+)/, 1]
            end
            out << NodeType.new(method, scope, priority, group, done)
	    end
    end
    out
end

$traceability = {}
["TranslationTests.java", "AdapterTests.java"].each do |file|
    $traceability.update parse_tests(file)
end

out = parse_boogie(File.read("../" + $boogie_path + "BoogieVisitor.java"))

puts "{{{"
puts "#!html"
puts TableEmitter.emit(out)
puts "}}}"

