#!/usr/bin/ruby

path = "../compiler/org/jmlspecs/jml4/boogie/"

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

class NodeType
    attr_reader :method, :scope, :priority, :group, :done

    def initialize(method, scope, priority, group = "misc", done = false)
        self.method = method
        self.scope = scope
        self.priority = Priority.new(priority)
        self.group = Group.new(group)
        self.done = done
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
                <th style='font-weight:bold' align='left' colspan='5'>
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
                 </tr>
            eof
        else
            style = ''
            if o.done
                style = 'background-color:#bea'
            elsif o.priority.colour
                style = 'color:'+o.priority.colour
            end

            <<-eof
                <tr style='#{style}'>
                    <td align='left'>#{i}</td>
                    <th align='left'>#{o.method}</th>
                    <td align='left'>#{o.scope}</td>
                    <td align='center'><strong>#{o.done ? 'X':''}</strong></td>
                    <td align='left'>#{o.priority.html}</td>
                </tr>
            eof
        end
    end
end

def parse(str)
    lines = str.split(/\r?\n/)
    out = []
    lines.each_with_index do |line, index|
	    if line =~ /public boolean visit\((\S+) term, (\S+) .+?\)/
		    method, scope, done, priority, group = $1, $2, true, nil, nil
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

out = parse(File.read(path + "BoogieVisitor.java"))

puts "{{{"
puts "#!html"
puts TableEmitter.emit(out)
puts "}}}"

