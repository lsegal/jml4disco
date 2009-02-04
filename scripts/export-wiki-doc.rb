#!/usr/bin/ruby
require 'rubygems'
require 'highline/import'
require 'net/https'
require 'open-uri'
require 'hpricot'
require 'fileutils'

# wiki documents to process
$wikidocs = { 
  'BiWeeklyStatusReport' => 'mgmt',
  'Proposal' => 'mgmt',
  'ActivityPlan' => 'mgmt',
  #'MeetingMinutes' => 'mgmt',
  'RiskManagement' => 'mgmt',
  'ProcessDocumentation' => 'mgmt',
  'ImpactAnalysis' => 'mgmt',
  'CachingStrategies' => 'research',
  'CachingEvaluation' => 'research',
  'LoadBalancing' => 'research',
  'PlanForDistributedReq' => 'research',
  'ProversBenchmark' => 'research',
  'ProfilingResults' => 'research',
  'VisionDocument' => 'reqs',
  'SupplementarySpecification' => 'reqs',
  'InstallationAndCommissioning' => 'reqs',
  'Glossary' => 'reqs',
  'Jml4-LogicalView' => 'design',
  'FirstPrototype' => 'design',
  'Jml4Disco-LogicalView' => 'design',
  'Jml4Disco-PhysicalView' => 'design',
  'Jml4Disco-UseCaseView' => 'design',
  'DevelopmentView' => 'design',
  'TestPlan' => 'test',
  'BoogieTraceability' => 'test'
  'BoogieTraceability' => 'test'
  'PerformanceReport' => 'test'
}
$categories = [
  ['mgmt', 'Management, Planning &amp; Risk Analysis Docs'],
  ['research', 'Research &amp; Potential Strategies Docs'],
  ['reqs', 'Requirements Docs'],
  ['design', 'Design &amp; Architecture'],
  ['test', 'Testing &amp; Implementation']
]

if i=ARGV.index('--user')
  $username = ARGV[$i + 1]
else 
  $username = ask("Enter your stu username: ") {|q| q.echo = true }
end
$password = ask("Enter your stu password: ") {|q| q.echo = "*" }
$base_url = "https://group0j.stu01.encs.concordia.ca:9443/trac/wiki/"
$open_opt = { :http_basic_authentication => [$username, $password] }

def doc_filename(document_name, category)
  category + '/' + document_name.gsub(/([a-z])([A-Z])/,'\1-\2').split(/\?/).first.downcase + '.html'
end

def process(document_name, category)

  filename = doc_filename(document_name, category)

  # common HTML elements to remove (expressed with css selectors)
  elements_to_remove = ["html > head > link",
                        "html > head > style",
                        "html > head > script",
                        "html > body > script",
                        "div#banner",
                        "div#header",
                        "div#search",
                        "div#ctxtnav",
                        "div#metanav",
                        "div#mainnav",
                        "div.buttons",
                        "div#altlinks",
                        "div#footer",
                        "h3#tkt-changes-hdr",
                        "ul.tkt-chg-list"]

  # process html and write file
  begin
    # load the wiki page
    response = open($base_url + document_name, $open_opt).read
	  doc = Hpricot(response)
  
    # search for each element and remove it from the doc
    elements_to_remove.each { |e| doc.search(e).remove }

    # set title
    doc.search("html > head").at("title").inner_html = "Disco - " + document_name.gsub(/([a-z])([A-Z])/,'\1 \2')
  
    # add link to css
    updir = "../" * category.split(/\//).size
    css = %Q(<link rel="stylesheet" type="text/css" href="#{updir}style.css" />)
    doc.search("html > head").append(css)

    # give toc's parent ol a class
    ol = doc.search("html > body > div.wiki-toc > ol").first
    ol.raw_attributes = ol.attributes.merge('class' => 'top-most') unless ol.nil?
    
    # change the toc's li's class names
    doc.search("html > body > div.wiki-toc > ol").search("li.active").set(:class => 'toc') rescue nil

    # create category directory if it does not exist
    FileUtils.mkdir_p(File.dirname(filename)) rescue nil

    # find all images
    doc.search("//img").each do |img|
        imgfile = img.attributes['src']
        short_imgfile = File.basename(imgfile).split(/\?/).first

        # change image attribute in source
        img.raw_attributes = img.attributes.merge("src" => File.join('images', short_imgfile))

        # make image directory
        outdir = File.join(File.dirname(filename), 'images')
        FileUtils.mkdir_p(outdir)

        # write image to file
        contents = open($base_url + '../../' + imgfile, $open_opt).read
        File.open(File.join(outdir, short_imgfile), "wb") do |f|
            f.write(contents)
        end
    end

    # write HTML to file
    File.open(filename, "w") { |f| f.write(doc.to_html) }
    print "wrote #{filename}... "
  rescue StandardError => bang
    print "(Oops! " + bang + ") "
  end
  
end

class Net::HTTP
    alias :old_verify_mode :verify_mode=
    def verify_mode=(x) old_verify_mode(OpenSSL::SSL::VERIFY_NONE) end
end

def write_pages
  $wikidocs.each do |name, category|
    print "Exporting \"" + name + "\"... "
    process(name, category)
    puts "done."
  end
end

def generate_index
  print "Exporting index..."
  index = <<-eof
    <html>
      <head>
        <title>JML4 Disco Documentation</title>
      </head>
      <body>
        <h1>JML4 Disco Documentation</h1>
  eof
  $categories.each do |row|
    cat, name = row.first, row.last
    index += "<h2>#{name}</h2>\n"
    index += "<ul>\n"
    $wikidocs.select {|k,v| v == cat }.each do |doc, cat|
      fname = doc_filename(doc, cat)
      index += "<li><a href='#{fname}'>#{doc}</a>\n"
    end
    index += "</ul>\n"
  end
  index += <<-eof
      </body>
    </html>
  eof
  File.open('index.html', "w") { |f| f.write(index) }
  
  puts "done."
end

write_pages unless ARGV.include?('--just-index')
generate_index if ARGV.include?('--no-index')