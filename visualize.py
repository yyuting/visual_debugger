import skimage
import skimage.io
import numpy as np
import pygame
import astunparse

def draw_basic_panel(rows=16, cols=16, color=[1, 0, 0]):
    """
    draw the basic panel that represents each pixel
    """
    unit_height = 32
    unit_width = 32
    
    height = rows * unit_height
    width = cols * unit_width
    
    output_img = np.ones([height, width, 3])
    
    if len(color) == 3:
        color = color / np.sqrt(color[0] ** 2 + color[1] ** 2 + color[2] ** 2)
    else:
        color = [1, 0, 0]
    
    output_img[:, :, 0] *= color[0] / 2
    output_img[:, :, 1] *= color[1] / 2
    output_img[:, :, 2] *= color[2] / 2
    
    output_img[0 : 2] = 0
    output_img[height - 2 : height] = 0
    
    for i in range(1, rows):
        output_img[i * unit_height - 2 : i * unit_height + 2] = 0
    
    output_img[:, 0 : 2] = 0
    output_img[:, width - 2 : width] = 0
    
    for j in range(1, cols):
        output_img[:, j * unit_width - 2 : j * unit_width + 2] = 0
    
    output = {'img': output_img, 'unit_height': unit_height, 'unit_width': unit_width, 'color': color, 'rows': rows, 'cols': cols}
    
    return output

def highlight_pixel(output, pixel_positions):
    """
    given a panel, highlight the pixels desired
    """
    
    try:
        if pixel_positions.shape[0] != 2:
            return output
    except:
        return output
    
    try:
        for i in range(pixel_positions.shape[1]):
        
            pixel_x = pixel_positions[i, 0]
            pixel_y = pixel_positions[i, 1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2]"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] *= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] *= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] *= 2
            
    except:
        try:
            pixel_x = pixel_positions[0]
            pixel_y = pixel_positions[1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2]"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] *= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] *= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] *= 2
        except:
            return output
        
    return output

def set_pixel_color(output, pixel_positions, color):
    
    try:
        if pixel_positions.shape[0] != 2:
            return output
    except:
        return output
    
    try:
        for i in range(pixel_positions.shape[1]):
        
            pixel_x = pixel_positions[i, 0]
            pixel_y = pixel_positions[i, 1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2]"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = color[0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = color[1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = color[2]
            
    except:
        try:
            pixel_x = pixel_positions[0]
            pixel_y = pixel_positions[1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2]"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = color[0]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = color[1]
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = color[2]
        except:
            return output
        
    return output

def dehighlight_pixel(output, pixel_positions):
    
    try:
        if pixel_positions.shape[0] != 2:
            return output
    except:
        return output
    
    try:
        for i in range(pixel_positions.shape[1]):
        
            pixel_x = pixel_positions[i, 0]
            pixel_y = pixel_positions[i, 1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0] / 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1] / 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2] / 2"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] /= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] /= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] /= 2
            
    except:
        try:
            pixel_x = pixel_positions[0]
            pixel_y = pixel_positions[1]
            real_x = pixel_x * output['unit_height']
            real_y = pixel_y * output['unit_width']
        
            """output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] = output['color'][0] / 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] = output['color'][1] / 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] = output['color'][2] / 2"""
            
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 0] /= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 1] /= 2
            output['img'][real_x + 2 : real_x + output['unit_height'] - 2, real_y + 2 : real_y + output['unit_width'] - 2, 2] /= 2
        
        except:
            return output
        
    return output

def loop_through_array(rows=16, cols=16, color=[1, 0, 0]):
    """
    create images that visualize the process of looping through the array
    """
    
    output = draw_basic_panel(rows, cols, color)
    
    old_pixel = np.array([])
    
    for i in range(rows):
        for j in range(cols):
            current_pixel = np.array([i, j])
            output = highlight_pixel(output, current_pixel)
            output = dehighlight_pixel(output, old_pixel)
            old_pixel = current_pixel
            skimage.io.imsave('visualization/test' + str(j + i * cols) + '.png', output['img'])
            
def show_input_output(rows=16, cols=16, color_in=[1, 0, 0], color_out=[0, 1, 0], direction=[]):
    """
    create images that shows the relation between an output array and an input array
    """
    
    input_array = draw_basic_panel(rows, cols, color_in)
    output_array = draw_basic_panel(rows, cols, color_out)
    
    output_img = np.zeros([input_array['img'].shape[0], input_array['img'].shape[1] * 2, 3])
    
    old_output_pixel = np.array([])
    old_input_pixel = [np.array([]) for i in range(len(direction))]
    
    for i in range(rows):
        for j in range(cols):
            
            #manipulate output, which iterates one pixel at a time
            output_array = dehighlight_pixel(output_array, old_output_pixel)
            old_output_pixel = np.array([i, j])
            output_array = highlight_pixel(output_array, old_output_pixel)
            
            #manipulate input, which is the current pixel shifting to the directions given
            for k in range(len(direction)):
                
                input_array = dehighlight_pixel(input_array, old_input_pixel[k])

                if direction[k][0] + i >= 0 and direction[k][1] + j >= 0 and direction[k][0] + i < rows and direction[k][1] + j < cols:
                    old_input_pixel[k] = np.array([direction[k][0] + i, direction[k][1] + j])
                    input_array = highlight_pixel(input_array, old_input_pixel[k])
                else:
                    old_input_pixel[k] = np.array([])
                    
            #combine input and output and write to file
            output_img[:, 0 : input_array['img'].shape[1], :] = output_array['img']
            output_img[:, input_array['img'].shape[1] : output_img.shape[1], :] = input_array['img']
            skimage.io.imsave('direction/test' + str(j + i * cols) + '.png', output_img)        
            
def animate_input_output(rows=16, cols=16, color_in=[1, 0, 0], color_out=[0, 1, 0], direction=[], title=''):
    """
    create images that shows the relation between an output array and an input array
    """
    
    input_array = draw_basic_panel(rows, cols, color_in)
    output_array = draw_basic_panel(rows, cols, color_out)
    
    output_img = np.zeros([input_array['img'].shape[0], input_array['img'].shape[1] * 2, 3])
    
    old_output_pixel = np.array([])
    old_input_pixel = [np.array([]) for i in range(len(direction))]
    
    pygame.init()
    
    screen = pygame.display.set_mode((output_img.shape[0], output_img.shape[1]))
    pygame.display.set_caption(title)
    
    while True:
    
        for i in range(rows):
            for j in range(cols):
            
                #manipulate output, which iterates one pixel at a time
                output_array = dehighlight_pixel(output_array, old_output_pixel)
                old_output_pixel = np.array([i, j])
                output_array = highlight_pixel(output_array, old_output_pixel)
            
                #manipulate input, which is the current pixel shifting to the directions given
                for k in range(len(direction)):
                
                    input_array = dehighlight_pixel(input_array, old_input_pixel[k])

                    if direction[k][0] + i >= 0 and direction[k][1] + j >= 0 and direction[k][0] + i < rows and direction[k][1] + j < cols:
                        old_input_pixel[k] = np.array([direction[k][0] + i, direction[k][1] + j])
                        input_array = highlight_pixel(input_array, old_input_pixel[k])
                    else:
                        old_input_pixel[k] = np.array([])
                    
                #combine input and output and write to file
                output_img[:, 0 : input_array['img'].shape[1], :] = output_array['img']
                output_img[:, input_array['img'].shape[1] : output_img.shape[1], :] = input_array['img']
                pygame.surfarray.blit_array(screen, output_img * 255)
                pygame.display.flip()
                pygame.time.wait(100)
                
def add_edge_info(output, radius_r, radius_c):
    
    for i in range(radius_r):
        for j in range(output['cols']):
            output = dehighlight_pixel(output, np.array([i, j]))
                                       
    for i in range(output['rows'] - radius_r, output['rows']):
        for j in range(output['cols']):
            output = dehighlight_pixel(output, np.array([i, j]))                   
    
    for i in range(radius_r, output['rows'] - radius_r):
        for j in range(radius_c):
            output = dehighlight_pixel(output, np.array([i, j]))
            
        for j in range(output['cols'] - radius_c, output['cols']):
            output = dehighlight_pixel(output, np.array([i, j]))
            
    return output
                
def animate_input_output_edge(rows=20, cols=20, color_in=[0.5, 0, 0], color_out=[0, 0.5, 0], direction=[], title='', radius_r=0, radius_c=0):
    """
    create images that shows the relation between an output array and an input array
    """
    
    out_of_boundary = False
    
    input_array = draw_basic_panel(rows, cols, color_in)
    output_array = draw_basic_panel(rows, cols, color_out)
    
    input_array = add_edge_info(input_array, radius_r, radius_c)
    output_array = add_edge_info(output_array, radius_r, radius_c)
    
    output_img = np.ones([input_array['img'].shape[0], input_array['img'].shape[1] * 2 + 32, 3])
    
    old_output_pixel = np.array([])
    old_input_pixel = [np.array([]) for i in range(len(direction))]
    
    pygame.init()
    
    screen = pygame.display.set_mode((output_img.shape[1], output_img.shape[0]))
    pygame.display.set_caption(title)
    
    while True:
    
        for i in range(rows):
            for j in range(cols):
            
                #manipulate output, which iterates one pixel at a time
                if out_of_boundary:
                    out_of_boundary = False
                else:
                    output_array = dehighlight_pixel(output_array, old_output_pixel)
                old_output_pixel = np.array([i, j])
                output_array = highlight_pixel(output_array, old_output_pixel)
            
                #manipulate input, which is the current pixel shifting to the directions given
                for k in range(len(direction)):
                
                    input_array = dehighlight_pixel(input_array, old_input_pixel[k])

                    if direction[k][0] + i >= 0 and direction[k][1] + j >= 0 and direction[k][0] + i < rows and direction[k][1] + j < cols:
                        old_input_pixel[k] = np.array([direction[k][0] + i, direction[k][1] + j])
                        input_array = highlight_pixel(input_array, old_input_pixel[k])
                    else:
                        old_input_pixel[k] = np.array([])
                        out_of_boundary = True
                    
                #combine input and output and write to file
                
                if out_of_boundary:
                    output_array = set_pixel_color(output_array, old_output_pixel, [1, 1, 1])
                output_img[:, 0 : input_array['img'].shape[1], :] = output_array['img']
                output_img[:, input_array['img'].shape[1] + 32 : output_img.shape[1], :] = input_array['img']
                pygame.surfarray.blit_array(screen, output_img.transpose((1, 0, 2)) * 255)
                pygame.display.flip()
                pygame.time.wait(50)
                
def animate_input_output_edge_condition_check(rows=20, cols=20, color_in=[0.5, 0, 0], color_out=[0, 0.5, 0], direction=[], title='', radius_r=0, radius_c=0, condition={}, read_nodes=None):
    """
    create images that shows the relation between an output array and an input array
    """
    
    out_of_boundary = False
    
    input_array = draw_basic_panel(rows, cols, color_in)
    output_array = draw_basic_panel(rows, cols, color_out)
    
    input_array = add_edge_info(input_array, radius_r, radius_c)
    output_array = add_edge_info(output_array, radius_r, radius_c)
    
    output_img = np.ones([input_array['img'].shape[0], input_array['img'].shape[1] * 2 + 32, 3])
    
    old_output_pixel = np.array([])
    old_input_pixel = [np.array([]) for i in range(len(direction))]
    
    pygame.init()
    
    screen = pygame.display.set_mode((output_img.shape[1], output_img.shape[0]))
    pygame.display.set_caption(title)
    
    while True:
    
        for i in range(rows):
            for j in range(cols):
            
                #manipulate output, which iterates one pixel at a time
                if out_of_boundary:
                    out_of_boundary = False
                else:
                    output_array = dehighlight_pixel(output_array, old_output_pixel)
                old_output_pixel = np.array([i, j])
                output_array = highlight_pixel(output_array, old_output_pixel)
            
                #manipulate input, which is the current pixel shifting to the directions given
                for k in range(len(direction)):
                
                    input_array = dehighlight_pixel(input_array, old_input_pixel[k])

                    if -direction[k][0] + i >= 0 and -direction[k][1] + j >= 0 and -direction[k][0] + i < rows and -direction[k][1] + j < cols:
                        old_input_pixel[k] = np.array([-direction[k][0] + i, -direction[k][1] + j])
                        input_array = highlight_pixel(input_array, old_input_pixel[k])
                    else:
                        old_input_pixel[k] = np.array([])
                        read_node = read_nodes[k]
                        if read_node in condition:
                            if i < radius_r:
                                fst = 0
                            elif i >= rows - radius_r:
                                fst = 2
                            else:
                                fst = 1
                            if j < radius_c:
                                snd = 0
                            elif j >= cols - radius_c:
                                snd = 2
                            else:
                                snd = 1
                            if not (fst, snd, False) in condition[read_node]:
                                out_of_boundary = True
                    
                #combine input and output and write to file
                
                if out_of_boundary:
                    output_array = set_pixel_color(output_array, old_output_pixel, [1, 1, 1])
                output_img[:, 0 : input_array['img'].shape[1], :] = output_array['img']
                output_img[:, input_array['img'].shape[1] + 32 : output_img.shape[1], :] = input_array['img']
                pygame.surfarray.blit_array(screen, output_img.transpose((1, 0, 2)) * 255)
                pygame.display.flip()
                pygame.time.wait(50)
                
def display_output_and_click(local_types, var_L, radius, read_nodes, condition):
    
    output_img = local_types['test_result']
    
    screen=pygame.display.set_mode((output_img.shape[1], output_img.shape[0]))
    pygame.surfarray.blit_array(screen, output_img.transpose((1, 0, 2)) * 255)
    pygame.display.flip()
    while True:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                sys.exit()
            if event.type == pygame.MOUSEBUTTONDOWN:
                x, y = event.pos
                if y < int(radius[0]):
                    fst = 0
                elif y >= output_img.shape[0] - int(radius[0]):
                    fst = 2
                else:
                    fst = 1
                if x < int(radius[1]):
                    snd = 0
                elif x >= output_img.shape[1] - int(radius[1]):
                    snd = 2
                else:
                    snd = 1
                    
                print('output[' + str(y) + ', ' + str(x) + '] is dependent on the following in current loop:')
                    
                for read_node in read_nodes:
                    if not (fst, snd, False) in condition[read_node]:
                        read_dump = astunparse.unparse(read_node.parent)[0 : -1]
                        read_dump = read_dump.replace(var_L[0], str(y))
                        read_dump = read_dump.replace(var_L[1], str(x))
                        print(read_dump + '   on line ' + str(read_node.lineno))
                
                print()

#show_input_output(direction=[[1, 2], [-1, -2]])

"""output = draw_basic_panel()

position = np.array([[1, 2], [3, 4]])

output = highlight_pixel(output, position)

output = dehighlight_pixel(output, position)

skimage.io.imsave('test.png', output['img'])"""

#loop_through_array()