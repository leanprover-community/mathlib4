changes = {}
while gets
  next if $_ !~ /info:.*(Mathlib[^:]+):.*Replacement.*old=([^\s]+).*new=([^\s]+).*byteIdx := (\d+).*byteIdx := (\d+)/

  file, old, new, start_idx, end_idx = $1, $2, $3, $4.to_i, $5.to_i

  changes[file] ||= []

  changes[file] << [old, new, start_idx, end_idx]
end

changes.each { |file, values|
  contents = File.open(file, "rb").read
  puts "Looking at #{file} #{values.uniq.length}"

  values.each { |old, new, start_idx, end_idx|
    if contents[start_idx, end_idx-start_idx] != old
      $stderr.puts "Contents dont match! #{file} #{start_idx}-#{end_idx}"
    end
  }

  starts = values.uniq.map { |_, _, start_idx, _| start_idx }
  if starts.length != starts.uniq.length
    puts "Unexpected generalization took multiple branches!"
    next
  end
 
  adjust = 0
  values.uniq.each { |old, new, start_idx, end_idx|
    if contents[start_idx + adjust, end_idx - start_idx] != old
      $stderr.puts "Contents dont match! #{file} #{start_idx}-#{end_idx} / adjust=#{adjust}"
      $stderr.puts contents[start_idx + adjust, end_idx - start_idx].inspect
      exit 0
    end

    contents[start_idx + adjust, end_idx - start_idx] = new
    adjust += new.length - old.length
  }

  File.open(file, "w") { |f| f.write contents }
}
